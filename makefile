VERSION = 1.0.0-SNAPSHOT

# some library paths
docs/%.html: %.agda
	agda $< --html --html-dir=./docs/

%.agdai: %.agda
	agda $<

.PHONY: hs/%
hs/%: src/%.agda
	agda --compile --compile-dir hs $<

all: lib Readme.agdai

docs/.git/:
	-rm -r docs/
	git clone --branch gh-pages git@github.com:metaborg/mj.agda.git docs/

gh-pages: docs/.git/ docs

docs: lib docs/Readme.html
	cp docs/Readme.html docs/index.html

### libraries
lib: lib/stdlib lib/stdlib++ lib/categories
	
.PHONY: lib/categories
lib/categories:
	git submodule update --init lib/categories
	cd lib/categories

lib/stdlib++:
	git submodule update --init lib/stdlib++

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

release:
	tar cvzf mj-$(VERSION).tar.gz --exclude-vcs src lib makefile NOTICE LICENSE Readme.agda .agda-lib
