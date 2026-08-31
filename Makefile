COURSE ?= MAT11001
DOCUMENT ?= notes
SOURCE := $(COURSE)/$(DOCUMENT).tex

.PHONY: all pdf watch clean

all: pdf

pdf:
	@test -f "$(SOURCE)" || { echo "Missing source: $(SOURCE)" >&2; exit 1; }
	latexmk -cd -pdf -synctex=1 -interaction=nonstopmode -file-line-error -halt-on-error "$(SOURCE)"

watch:
	@test -f "$(SOURCE)" || { echo "Missing source: $(SOURCE)" >&2; exit 1; }
	latexmk -cd -pdf -pvc -synctex=1 -interaction=nonstopmode -file-line-error -halt-on-error "$(SOURCE)"

clean:
	@test -f "$(SOURCE)" || { echo "Missing source: $(SOURCE)" >&2; exit 1; }
	latexmk -cd -c "$(SOURCE)"
