# some library paths
docs/%.html: %.agda
	agda $< --html --html-dir=./docs/

%.agdai: %.agda
	agda $<

all: lib Readme.agdai

docs/.git/:
	-rm -r docs/
	git clone --branch gh-pages git@github.com:metaborg/mj.agda.git docs/

gh-pages: docs/.git/ docs

docs: lib docs/Readme.html
	cp docs/Readme.html docs/index.html

### libraries
lib: lib/stdlib lib/stdlib++

.PHONY: lib/stdlib++
lib/stdlib++:
	git submodule update --init lib/stdlib++

.PHONY: lib/stdlib
lib/stdlib:
	git submodule update --init lib/stdlib

.PHONY: assumptions
assumptions:
	git grep --color -Hi "postulate" -- "src/**/*.agda"
	git grep --color -Hi "TERMINATING" -- "src/**/*.agda"

### cleaning
.PHONY: clean clean-all
clean:
	-rm Readme.agdai
	-cd src && find . -iname '*.agdai' -exec rm {} \;

clean-all: clean
	rm -rf lib
