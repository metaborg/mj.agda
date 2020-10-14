VERSION = 1.0.0-SNAPSHOT

AGDA = agda -W noDeprecationWarning

# some library paths
docs/%.html: %.agda
	$(AGDA) $< --html --html-dir=./docs/

%.agdai: %.agda
	$(AGDA) $<

all: lib Readme.agdai

docs/.git/:
	-rm -r docs/
	git clone --branch gh-pages git@github.com:metaborg/mj.agda.git docs/

gh-pages: docs/.git/ docs

docs: lib docs/Readme.html
	cp docs/Readme.html docs/index.html

### libraries
lib: lib/stdlib/.git

lib/stdlib/.git:
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
	git clone . build
	cd build && make lib && \
	tar cvzf ../mj-$(VERSION).tar.gz --exclude=*.agdai --exclude-vcs src lib makefile NOTICE LICENSE Readme.agda .agda-lib
	rm -rf build
