COURSE ?= MAT11003
DOCUMENT ?= notes
SOURCE := $(COURSE)/$(DOCUMENT).tex
SOURCES := $(wildcard */*.tex)
PDFS := $(SOURCES:.tex=.pdf)

.PHONY: all pdf watch clean

all: $(PDFS)

%.pdf: %.tex preamble.tex
	latexmk -cd -pdf -synctex=1 -interaction=nonstopmode -file-line-error -halt-on-error "$<"

pdf:
	@test -f "$(SOURCE)" || { echo "Missing source: $(SOURCE)" >&2; exit 1; }
	latexmk -cd -pdf -synctex=1 -interaction=nonstopmode -file-line-error -halt-on-error "$(SOURCE)"

watch:
	@test -f "$(SOURCE)" || { echo "Missing source: $(SOURCE)" >&2; exit 1; }
	latexmk -cd -pdf -pvc -synctex=1 -interaction=nonstopmode -file-line-error -halt-on-error "$(SOURCE)"

clean:
	@test -f "$(SOURCE)" || { echo "Missing source: $(SOURCE)" >&2; exit 1; }
	latexmk -norc -cd -c "$(SOURCE)"
	rm -rf "$(COURSE)/.latex-build"
