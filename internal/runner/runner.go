// Package runner provides the standalone tsgolint linting entry point.
// Accepts a slice of rules and CLI args, handles tsconfig resolution,
// TypeScript program creation, parallel linting, and diagnostic output.
//
// --fix support: when enabled, diagnostics are collected per-file instead of
// streamed. After linting completes, ApplyRuleFixes is called per file and
// the fixed source is written back to disk. Only unfixed diagnostics are printed.
//
// --warn support: rules listed via --warn <name> are treated as warnings.
// Warnings are displayed with a yellow header instead of the default bold style.
// Only errors (non-warning diagnostics) cause exit code 1. Warnings alone
// produce exit code 0 so they don't fail CI.
//
// --warn-file support: warnings are only printed for files matching
// the given absolute paths. Warnings for all other files are silently
// skipped. This keeps output focused on new/changed code in large codebases.
// When no --warn-file flags are given, NO warnings are shown (not all).
// Use --all-warnings to bypass this filter and show warnings everywhere.
package runner

import (
	"bufio"
	"flag"
	"fmt"
	"math"
	"os"
	"path/filepath"
	"runtime"
	"runtime/pprof"
	"runtime/trace"
	"slices"
	"strconv"
	"strings"
	"sync"
	"time"
	"unicode"

	"github.com/typescript-eslint/tsgolint/internal/diagnostic"
	"github.com/typescript-eslint/tsgolint/internal/linter"
	"github.com/typescript-eslint/tsgolint/internal/rule"
	"github.com/typescript-eslint/tsgolint/internal/utils"

	"github.com/microsoft/typescript-go/shim/ast"
	"github.com/microsoft/typescript-go/shim/bundled"
	"github.com/microsoft/typescript-go/shim/core"
	"github.com/microsoft/typescript-go/shim/scanner"
	"github.com/microsoft/typescript-go/shim/tspath"
	"github.com/microsoft/typescript-go/shim/vfs/cachedvfs"
	"github.com/microsoft/typescript-go/shim/vfs/osvfs"
)

// fileDiagnostics groups all diagnostics for a single source file so
// ApplyRuleFixes can process them together when --fix is enabled.
type fileDiagnostics struct {
	sourceFile  *ast.SourceFile
	diagnostics []rule.RuleDiagnostic
}

const spaces = "                                                                                                    "

// stringSlice implements flag.Value for repeatable string flags.
// Usage: flagSet.Var(&warnRules, "warn", "treat rule as warning")
// Allows: --warn rule-a --warn rule-b
type stringSlice []string

func (s *stringSlice) String() string { return strings.Join(*s, ",") }
func (s *stringSlice) Set(v string) error {
	*s = append(*s, v)
	return nil
}

// Run executes the linter with the given rules and CLI args.
// Returns the process exit code (0 = no errors, 1 = errors or failure).
func Run(rules []rule.Rule, args []string) int {
	flagSet := flag.NewFlagSet("lintcn", flag.ContinueOnError)
	var (
		help           bool
		fix            bool
		tsconfig       string
		listFiles      bool
		traceOut       string
		cpuprofOut     string
		singleThreaded bool
		allWarnings    bool
		warnRules      stringSlice
		warnFiles      stringSlice
	)
	flagSet.StringVar(&tsconfig, "tsconfig", "", "which tsconfig to use")
	flagSet.BoolVar(&listFiles, "list-files", false, "list matched files")
	flagSet.BoolVar(&fix, "fix", false, "automatically fix violations and write files back to disk")
	flagSet.BoolVar(&help, "help", false, "show help")
	flagSet.BoolVar(&help, "h", false, "show help")
	flagSet.StringVar(&traceOut, "trace", "", "file to write trace to")
	flagSet.StringVar(&cpuprofOut, "cpuprof", "", "file to write cpu profile to")
	flagSet.BoolVar(&singleThreaded, "singleThreaded", false, "run in single threaded mode")
	flagSet.Var(&warnRules, "warn", "treat this rule as a warning (can be repeated)")
	flagSet.Var(&warnFiles, "warn-file", "only show warnings for this file (can be repeated, absolute paths)")
	flagSet.BoolVar(&allWarnings, "all-warnings", false, "show warnings for all files, bypass --warn-file filter")
	if err := flagSet.Parse(args); err != nil {
		return 1
	}
	if help {
		fmt.Fprint(os.Stderr, " lintcn — type-aware TypeScript linter\n\nUsage:\n    lintcn [OPTIONS]\n\nOptions:\n    --tsconfig PATH   Which tsconfig to use. Defaults to tsconfig.json.\n    --fix             Automatically fix violations\n    --warn NAME       Treat rule as warning, not error (repeatable)\n    --warn-file PATH  Only show warnings for this file (repeatable, absolute)\n    --all-warnings    Show warnings for all files (bypass --warn-file filter)\n    --list-files      List matched files\n    -h, --help        Show help\n")
		return 0
	}

	// Build set of rule names that should be treated as warnings.
	warningRulesSet := map[string]bool{}
	for _, name := range warnRules {
		warningRulesSet[name] = true
	}

	// Build set of absolute file paths where warnings should be shown.
	// Paths are normalized with tspath (forward slashes) to match SourceFile.FileName().
	warnFilesSet := map[string]bool{}
	for _, f := range warnFiles {
		warnFilesSet[tspath.NormalizePath(f)] = true
	}

	enableVirtualTerminalProcessing()
	timeBefore := time.Now()

	if done, err := recordTrace(traceOut); err != nil {
		os.Stderr.WriteString(err.Error())
		return 1
	} else {
		defer done()
	}
	if done, err := recordCpuprof(cpuprofOut); err != nil {
		os.Stderr.WriteString(err.Error())
		return 1
	} else {
		defer done()
	}

	currentDirectory, err := os.Getwd()
	if err != nil {
		fmt.Fprintf(os.Stderr, "error getting current directory: %v\n", err)
		return 1
	}
	currentDirectory = tspath.NormalizePath(currentDirectory)

	fs := bundled.WrapFS(cachedvfs.From(osvfs.FS()))
	var configFileName string
	if tsconfig == "" {
		configFileName = tspath.ResolvePath(currentDirectory, "tsconfig.json")
		if !fs.FileExists(configFileName) {
			fs = utils.NewOverlayVFS(fs, map[string]string{
				configFileName: "{}",
			})
		}
	} else {
		configFileName = tspath.ResolvePath(currentDirectory, tsconfig)
		if !fs.FileExists(configFileName) {
			fmt.Fprintf(os.Stderr, "error: tsconfig %q doesn't exist", tsconfig)
			return 1
		}
	}

	currentDirectory = tspath.GetDirectoryPath(configFileName)
	host := utils.CreateCompilerHost(currentDirectory, fs)
	comparePathOptions := tspath.ComparePathsOptions{
		CurrentDirectory:          host.GetCurrentDirectory(),
		UseCaseSensitiveFileNames: host.FS().UseCaseSensitiveFileNames(),
	}

	program, _, err := utils.CreateProgram(singleThreaded, fs, currentDirectory, configFileName, host, false)
	if err != nil {
		fmt.Fprintf(os.Stderr, "error creating TS program: %v", err)
		return 1
	}
	if program == nil {
		fmt.Fprintf(os.Stderr, "error creating TS program")
		return 1
	}

	files := []*ast.SourceFile{}
	cwdPath := string(tspath.ToPath("", currentDirectory, program.Host().FS().UseCaseSensitiveFileNames()).EnsureTrailingDirectorySeparator())
	var matchedFiles strings.Builder
	for _, file := range program.SourceFiles() {
		p := string(file.Path())
		if strings.Contains(p, "/node_modules/") {
			continue
		}
		if fileName, matched := strings.CutPrefix(p, cwdPath); matched {
			if listFiles {
				matchedFiles.WriteString("Found file: ")
				matchedFiles.WriteString(fileName)
				matchedFiles.WriteByte('\n')
			}
			files = append(files, file)
		}
	}
	if listFiles {
		os.Stdout.WriteString(matchedFiles.String())
	}
	slices.SortFunc(files, func(a *ast.SourceFile, b *ast.SourceFile) int {
		return len(b.Text()) - len(a.Text())
	})

	// shouldShowWarning decides whether a warning diagnostic should be printed.
	// - --all-warnings: show all warnings
	// - --warn-file provided: show only for files in the set (absolute path match)
	// - no --warn-file and no --all-warnings: show no warnings
	shouldShowWarning := func(d rule.RuleDiagnostic) bool {
		if allWarnings {
			return true
		}
		if len(warnFilesSet) == 0 {
			return false
		}
		return warnFilesSet[d.SourceFile.FileName()]
	}

	// --- diagnostic collection ---
	// When --fix is set we collect diagnostics per-file so we can apply fixes
	// after linting completes. Otherwise we stream-print as before.
	var wg sync.WaitGroup
	diagnosticsChan := make(chan rule.RuleDiagnostic, 4096)
	errorsCount := 0
	warningsCount := 0

	// Per-file collector used only in --fix mode.
	var (
		filesMu      sync.Mutex
		filesFixMap  = map[string]*fileDiagnostics{}
		fixFileOrder []string // preserves first-seen order for deterministic output
	)

	onDiagnostic := func(d rule.RuleDiagnostic) {
		if fix {
			filesMu.Lock()
			fn := d.SourceFile.FileName()
			fd, exists := filesFixMap[fn]
			if !exists {
				fd = &fileDiagnostics{sourceFile: d.SourceFile}
				filesFixMap[fn] = fd
				fixFileOrder = append(fixFileOrder, fn)
			}
			fd.diagnostics = append(fd.diagnostics, d)
			filesMu.Unlock()
		} else {
			diagnosticsChan <- d
		}
	}

	// Stream-print goroutine (only used when --fix is NOT set).
	if !fix {
		wg.Go(func() {
			w := bufio.NewWriterSize(os.Stdout, 4096*100)
			defer w.Flush()
			totalCount := 0
			for d := range diagnosticsChan {
				isWarning := warningRulesSet[d.RuleName]
				if isWarning && !shouldShowWarning(d) {
					continue
				}
				if isWarning {
					warningsCount++
				} else {
					errorsCount++
				}
				totalCount++
				if totalCount == 1 {
					w.WriteByte('\n')
				}
				printDiagnostic(d, isWarning, w, comparePathOptions)
				if w.Available() < 4096 {
					w.Flush()
				}
			}
		})
	}

	err = linter.RunLinterOnProgram(
		utils.GetLogLevel(),
		program,
		files,
		runtime.GOMAXPROCS(0),
		func(sourceFile *ast.SourceFile) []linter.ConfiguredRule {
			return utils.Map(rules, func(r rule.Rule) linter.ConfiguredRule {
				return linter.ConfiguredRule{
					Name: r.Name,
					Run: func(ctx rule.RuleContext) rule.RuleListeners {
						return r.Run(ctx, nil)
					},
				}
			})
		},
		onDiagnostic,
		func(d diagnostic.Internal) {},
		linter.Fixes{Fix: true, FixSuggestions: !fix},
		linter.TypeErrors{ReportSyntactic: false, ReportSemantic: false},
	)
	if !fix {
		close(diagnosticsChan)
	}
	if err != nil {
		fmt.Fprintf(os.Stderr, "error running linter: %v\n", err)
		return 1
	}
	wg.Wait()

	// --- apply fixes when --fix is set ---
	fixedFilesCount := 0
	if fix {
		// Sort file names for deterministic output across runs (concurrent
		// workers emit diagnostics in arbitrary order).
		slices.Sort(fixFileOrder)

		w := bufio.NewWriterSize(os.Stdout, 4096*100)
		firstError := true
		for _, fn := range fixFileOrder {
			fd := filesFixMap[fn]

			// Filter out warnings that shouldn't be shown BEFORE applying fixes.
			// This prevents warning auto-fixes from silently modifying files
			// that aren't in the --warn-file list.
			eligible := make([]rule.RuleDiagnostic, 0, len(fd.diagnostics))
			for _, d := range fd.diagnostics {
				isWarning := warningRulesSet[d.RuleName]
				if isWarning && !shouldShowWarning(d) {
					continue
				}
				eligible = append(eligible, d)
			}

			fixedCode, unapplied, wasFixed := linter.ApplyRuleFixes(fd.sourceFile.Text(), eligible)
			if wasFixed {
				// tspath uses forward slashes; convert to OS path for writing.
				osPath := filepath.FromSlash(fn)
				if writeErr := os.WriteFile(osPath, []byte(fixedCode), 0o644); writeErr != nil {
					fmt.Fprintf(os.Stderr, "error writing fixed file %s: %v\n", fn, writeErr)
					// Write failed — report all original diagnostics as remaining
					// so the user doesn't get a false "clean" result.
					unapplied = eligible
				} else {
					fixedFilesCount++
				}
			}
			// Print remaining unfixed diagnostics.
			for _, d := range unapplied {
				isWarning := warningRulesSet[d.RuleName]
				if isWarning {
					warningsCount++
				} else {
					errorsCount++
				}
				if firstError {
					w.WriteByte('\n')
					firstError = false
				}
				printDiagnostic(d, isWarning, w, comparePathOptions)
				if w.Available() < 4096 {
					w.Flush()
				}
			}
		}
		w.Flush()
	}

	// --- summary ---
	filesText := "files"
	if len(files) == 1 {
		filesText = "file"
	}
	rulesText := "rules"
	if len(rules) == 1 {
		rulesText = "rule"
	}
	threadsCount := 1
	if !singleThreaded {
		threadsCount = runtime.GOMAXPROCS(0)
	}

	// Build the "Found X errors and Y warnings" summary part.
	summaryParts := formatSummary(errorsCount, warningsCount)

	lintStats := fmt.Sprintf(
		" \x1b[2m(linted \x1b[1m%v\x1b[22m\x1b[2m %v with \x1b[1m%v\x1b[22m\x1b[2m %v in \x1b[1m%v\x1b[22m\x1b[2m using \x1b[1m%v\x1b[22m\x1b[2m threads)\n",
		len(files), filesText, len(rules), rulesText,
		time.Since(timeBefore).Round(time.Millisecond), threadsCount,
	)

	if fix && fixedFilesCount > 0 {
		fixedFilesText := "files"
		if fixedFilesCount == 1 {
			fixedFilesText = "file"
		}
		fmt.Fprintf(os.Stdout,
			"Fixed \x1b[1;32m%v\x1b[0m %v, %v remaining%v",
			fixedFilesCount, fixedFilesText, summaryParts, lintStats,
		)
	} else {
		fmt.Fprintf(os.Stdout, "Found %v%v", summaryParts, lintStats)
	}

	// Exit code 1 only when there are errors. Warnings alone don't fail CI.
	if errorsCount > 0 {
		return 1
	}
	return 0
}

// formatSummary builds a colored "X errors and Y warnings" string.
// Only includes parts that are non-zero, e.g. "2 errors", "3 warnings",
// or "2 errors and 3 warnings". When both are zero, returns green "0 errors".
func formatSummary(errorsCount, warningsCount int) string {
	var parts []string

	if errorsCount > 0 {
		errorsText := "errors"
		if errorsCount == 1 {
			errorsText = "error"
		}
		// Bold red for errors
		parts = append(parts, fmt.Sprintf("\x1b[1;31m%v\x1b[0m %v", errorsCount, errorsText))
	}

	if warningsCount > 0 {
		warningsText := "warnings"
		if warningsCount == 1 {
			warningsText = "warning"
		}
		// Bold yellow for warnings
		parts = append(parts, fmt.Sprintf("\x1b[1;33m%v\x1b[0m %v", warningsCount, warningsText))
	}

	if len(parts) == 0 {
		// All clean — green zero
		return "\x1b[1;32m0\x1b[0m errors"
	}

	return strings.Join(parts, " and ")
}

func utf16LineLengthWithoutLineTerminator(text string, lineMap []core.TextPos, line int) core.UTF16Offset {
	lineStart := int(lineMap[line])
	lineEnd := len(text)
	if line+1 < len(lineMap) {
		lineEnd = int(lineMap[line+1])
	}
	lineText := strings.TrimSuffix(text[lineStart:lineEnd], "\n")
	lineText = strings.TrimSuffix(lineText, "\r")
	return core.UTF16Len(lineText)
}

func printDiagnostic(d rule.RuleDiagnostic, isWarning bool, w *bufio.Writer, comparePathOptions tspath.ComparePathsOptions) {
	diagnosticStart := d.Range.Pos()
	diagnosticEnd := d.Range.End()
	diagnosticStartLine, diagnosticStartColumn := scanner.GetECMALineAndUTF16CharacterOfPosition(d.SourceFile, diagnosticStart)
	diagnosticEndline, _ := scanner.GetECMALineAndUTF16CharacterOfPosition(d.SourceFile, diagnosticEnd)
	lineMap := d.SourceFile.ECMALineMap()
	text := d.SourceFile.Text()
	codeboxStartLine := max(diagnosticStartLine-1, 0)
	codeboxEndLine := min(diagnosticEndline+1, len(lineMap)-1)
	codeboxStart := scanner.GetECMAPositionOfLineAndUTF16Character(d.SourceFile, codeboxStartLine, 0)
	codeboxEndColumn := utf16LineLengthWithoutLineTerminator(text, lineMap, codeboxEndLine)
	codeboxEnd := scanner.GetECMAPositionOfLineAndUTF16Character(d.SourceFile, codeboxEndLine, codeboxEndColumn)
	severityPrefix := "error "
	if isWarning {
		severityPrefix = "warning "
		// Yellow background, bold, white text for warnings
		w.Write([]byte{' ', 0x1b, '[', '7', 'm', 0x1b, '[', '1', 'm', 0x1b, '[', '3', '3', 'm', ' '})
	} else {
		// Default: inverted bold white (existing style for errors)
		w.Write([]byte{' ', 0x1b, '[', '7', 'm', 0x1b, '[', '1', 'm', 0x1b, '[', '3', '8', ';', '5', ';', '3', '7', 'm', ' '})
	}
	w.WriteString(severityPrefix)
	w.WriteString(d.RuleName)
	w.WriteString(" \x1b[0m — ")
	messageLineStart := 0
	for i, char := range d.Message.Description {
		if char == '\n' {
			w.WriteString(d.Message.Description[messageLineStart : i+1])
			messageLineStart = i + 1
			w.WriteString("    \x1b[2m│\x1b[0m")
			w.WriteString(spaces[:len(severityPrefix)+len(d.RuleName)+1])
		}
	}
	if messageLineStart <= len(d.Message.Description) {
		w.WriteString(d.Message.Description[messageLineStart:len(d.Message.Description)])
	}
	w.WriteString("\n  \x1b[2m╭─┴──────────(\x1b[0m \x1b[3m\x1b[38;5;117m")
	w.WriteString(tspath.ConvertToRelativePath(d.SourceFile.FileName(), comparePathOptions))
	w.WriteByte(':')
	w.WriteString(strconv.Itoa(diagnosticStartLine + 1))
	w.WriteByte(':')
	w.WriteString(strconv.Itoa(int(diagnosticStartColumn) + 1))
	w.WriteString("\x1b[0m \x1b[2m)─────\x1b[0m\n")
	indentSize := math.MaxInt
	line := codeboxStartLine
	lineIndentCalculated := false
	lastNonSpaceIndex := -1
	lineStarts := make([]int, 13)
	lineEnds := make([]int, 13)
	if codeboxEndLine-codeboxStartLine >= len(lineEnds) {
		w.WriteString("  \x1b[2m│\x1b[0m  Error range is too big. Skipping code block printing.\n  \x1b[2m╰────────────────────────────────\x1b[0m\n\n")
		return
	}
	for i, char := range text[codeboxStart:codeboxEnd] {
		if char == '\n' {
			if line != codeboxEndLine {
				lineIndentCalculated = false
				lineEnds[line-codeboxStartLine] = lastNonSpaceIndex - int(lineMap[line]) + codeboxStart
				lastNonSpaceIndex = -1
				line++
			}
			continue
		}
		if !lineIndentCalculated && !unicode.IsSpace(char) {
			lineIndentCalculated = true
			lineStarts[line-codeboxStartLine] = i - int(lineMap[line]) + codeboxStart
			indentSize = min(indentSize, lineStarts[line-codeboxStartLine])
		}
		if lineIndentCalculated && !unicode.IsSpace(char) {
			lastNonSpaceIndex = i + 1
		}
	}
	if line == codeboxEndLine {
		lineEnds[line-codeboxStartLine] = lastNonSpaceIndex - int(lineMap[line]) + codeboxStart
	}
	diagnosticHighlightActive := false
	lastLineNumber := strconv.Itoa(codeboxEndLine + 1)
	for line := codeboxStartLine; line <= codeboxEndLine; line++ {
		w.WriteString("  \x1b[2m│ ")
		if line == codeboxEndLine {
			w.WriteString(lastLineNumber)
		} else {
			number := strconv.Itoa(line + 1)
			if len(number) < len(lastLineNumber) {
				w.WriteByte(' ')
			}
			w.WriteString(number)
		}
		w.WriteString(" │\x1b[0m  ")
		lineTextStart := int(lineMap[line]) + indentSize
		underlineStart := max(lineTextStart, int(lineMap[line])+lineStarts[line-codeboxStartLine])
		underlineEnd := underlineStart
		lineTextEnd := max(int(lineMap[line])+lineEnds[line-codeboxStartLine], lineTextStart)
		if diagnosticHighlightActive {
			underlineEnd = lineTextEnd
		} else if int(lineMap[line]) <= diagnosticStart && (line == len(lineMap) || diagnosticStart < int(lineMap[line+1])) {
			underlineStart = min(max(lineTextStart, diagnosticStart), lineTextEnd)
			underlineEnd = lineTextEnd
			diagnosticHighlightActive = true
		}
		if int(lineMap[line]) <= diagnosticEnd && (line == len(lineMap) || diagnosticEnd < int(lineMap[line+1])) {
			underlineEnd = min(max(underlineStart, diagnosticEnd), lineTextEnd)
			diagnosticHighlightActive = false
		}
		if underlineStart != underlineEnd {
			w.WriteString(text[lineTextStart:underlineStart])
			if isWarning {
				// Yellow curly underline + yellow text for warnings (color 178 = dark yellow/gold)
				w.Write([]byte{0x1b, '[', '4', 'm', 0x1b, '[', '4', ':', '3', 'm', 0x1b, '[', '5', '8', ':', '5', ':', '1', '7', '8', 'm', 0x1b, '[', '3', '8', ';', '5', ';', '1', '7', '8', 'm', 0x1b, '[', '2', '2', ';', '4', '9', 'm'})
			} else {
				// Cyan/teal curly underline for errors (existing style, color 196)
				w.Write([]byte{0x1b, '[', '4', 'm', 0x1b, '[', '4', ':', '3', 'm', 0x1b, '[', '5', '8', ':', '5', ':', '1', '9', '6', 'm', 0x1b, '[', '3', '8', ';', '5', ';', '1', '9', '6', 'm', 0x1b, '[', '2', '2', ';', '4', '9', 'm'})
			}
			w.WriteString(text[underlineStart:underlineEnd])
			w.Write([]byte{0x1b, '[', '0', 'm'})
			w.WriteString(text[underlineEnd:lineTextEnd])
		} else if lineTextStart != lineTextEnd {
			w.WriteString(text[lineTextStart:lineTextEnd])
		}
		w.WriteByte('\n')
	}
	w.WriteString("  \x1b[2m╰────────────────────────────────\x1b[0m\n\n")
}

func recordTrace(traceOut string) (func(), error) {
	if traceOut == "" {
		return func() {}, nil
	}
	f, err := os.Create(traceOut)
	if err != nil {
		return nil, fmt.Errorf("error creating trace file: %w", err)
	}
	trace.Start(f)
	return func() { trace.Stop(); f.Close() }, nil
}

func recordCpuprof(cpuprofOut string) (func(), error) {
	if cpuprofOut == "" {
		return func() {}, nil
	}
	f, err := os.Create(cpuprofOut)
	if err != nil {
		return nil, fmt.Errorf("error creating cpuprof file: %w", err)
	}
	if err := pprof.StartCPUProfile(f); err != nil {
		return nil, fmt.Errorf("error starting cpu profiling: %w", err)
	}
	return func() { pprof.StopCPUProfile(); f.Close() }, nil
}
