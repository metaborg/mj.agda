# some library paths
STDPP = lib/stdlib++.agda
STDPP-REV = dd4b86f6c666a
AGDALIB = lib/agda

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
	cp docs/{Readme.html,index.html}

### libraries
lib: lib/agda/std-lib lib/stdlib++.agda

lib/stdlib++.agda:
	git clone -b 2.6 https://github.com/ElessarWebb/stdlib-plusplus.agda.git $(STDPP)
	cd $(STDPP) && git reset --hard $(STDPP-REV)

# checkout the compatible agda release source
lib/agda:
	git clone -b release-2.5.3 https://github.com/agda/agda/ $(AGDALIB)

# build the stdlib compatible with the agda release we're using
lib/agda/std-lib: lib/agda
	cd $(AGDALIB) && make fast-forward-std-lib

assumptions:
	git grep --color -Hi "postulate" -- "src/**/*.agda"
	git grep --color -Hi "TERMINATING" -- "src/**/*.agda"

### cleaning
.PHONY: clean clean-all
clean:
	cd src && find . -iname '*.agdai' -exec rm {} \;

clean-all: clean
	rm -rf lib
