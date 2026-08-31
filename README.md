# University Mathematics Notes

LaTeX sources and compiled notes for University of Helsinki mathematics
courses.

## Building

For example, to build the `MAT11001` notes:

```sh
make
```

The course and document can be selected explicitly:

```sh
make COURSE=MAT11001 DOCUMENT=notes
```

Use `make watch COURSE=MAT11001 DOCUMENT=notes` for continuous compilation and
`make clean COURSE=MAT11001 DOCUMENT=notes` to remove auxiliary files. Cleaning
preserves the final PDF because PDFs are kept under version control.

Without an active development shell, run a command through Nix directly:

```sh
nix develop -c make
```

## VimTeX

Start Vim or Neovim from the activated Nix or direnv environment, then open the
main document:

```sh
nvim MAT11001/notes.tex
```

VimTeX uses `latexmk` for continuous compilation. Run `:VimtexCompile` or the
default `\ll` mapping to start or stop compilation, and use `:VimtexView` or
`\lv` to open the configured PDF viewer. The source declares pdfLaTeX with a
TeX magic comment, keeps SyncTeX data beside the PDF, and loads the shared
preamble relative to the course directory, so no repository-specific VimTeX
configuration is required.

If the compiler method is overridden in the editor configuration, set it back
to `latexmk`:

```vim
let g:vimtex_compiler_method = 'latexmk'
```

## Adding A Course

Create a directory named after the course code and add `notes.tex` and any
exercise-set sources directly to it. Main documents should begin with:

```tex
% !TeX program = pdflatex
\documentclass[12pt,a4paper]{article}
\input{../preamble.tex}
```

For example, `MAT11001/exercise-01.tex` builds with:

```sh
make COURSE=MAT11001 DOCUMENT=exercise-01
```

Documents are in English by default. To use Finnish headings, theorem names,
cross-references, and hyphenation, select the language before loading the shared
preamble:

```tex
\newcommand{\notelanguage}{finnish}
\input{../preamble.tex}
```

Exercise solution documents can use the `exercise` and `solution`
environments. See `MAT11001/exercise-01.tex` for the first Finnish example.
