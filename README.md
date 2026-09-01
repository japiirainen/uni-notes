# University Mathematics Notes

Notes and exercise solutions for University of Helsinki mathematics
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
