# some library paths
STDPP = lib/stdlib++.agda
AGDALIB = lib/agda

docs/%.html: %.agda
	agda $< --html --html-dir=./docs/

%.agdai: %.agda
	agda $<

all: lib src/Readme.agdai

docs: lib docs/src/Everything.html docs/Readme.html
	cp docs/{Readme.html,index.html}

### libraries
lib: lib/agda/std-lib lib/stdlib++.agda lib-update

.PHONY: lib-update
lib-update:
	cd $(STDPP) && git pull

lib/stdlib++.agda:
	git clone -b 2.6 https://github.com/ElessarWebb/stdlib-plusplus.agda.git $(STDPP)

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
