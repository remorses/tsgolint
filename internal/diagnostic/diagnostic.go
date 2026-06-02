package diagnostic

import (
	"fmt"
	"io"
	"strings"

	"github.com/microsoft/typescript-go/shim/core"
)

type Internal struct {
	Range       core.TextRange
	Id          string
	Description string
	Help        string
	FilePath    *string `json:"omitempty"`
}

func WriteInternal(w io.Writer, d Internal) {
	fmt.Fprintf(w, "  %s: %s\n", d.Id, d.Description)
	if d.FilePath != nil && *d.FilePath != "" {
		fmt.Fprintf(w, "    file: %s\n", *d.FilePath)
	}
	if d.Range.Pos() != 0 || d.Range.End() != 0 {
		fmt.Fprintf(w, "    range: %d..%d\n", d.Range.Pos(), d.Range.End())
	}
	if d.Help != "" {
		for _, line := range strings.Split(d.Help, "\n") {
			fmt.Fprintf(w, "    %s\n", line)
		}
	}
}
