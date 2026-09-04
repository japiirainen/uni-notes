# University Mathematics Notes

Notes and exercise solutions for University of Helsinki mathematics
courses.

## Building

To build every PDF in the project:

```sh
make
```

To build one PDF, select the course and document explicitly:

```sh
make COURSE=MAT11001 DOCUMENT=notes
```

Use `make watch COURSE=MAT11001 DOCUMENT=notes` for continuous compilation and
`make clean COURSE=MAT11001 DOCUMENT=notes` to remove auxiliary files. Cleaning
preserves the final PDF because PDFs are kept under version control. Builds use
isolated temporary directories so readers only see the output of a completed
compilation.

Without an active development shell, run a command through Nix directly:

```sh
nix develop -c make
```
