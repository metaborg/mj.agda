# some library paths
STDPP = lib/stdlib++.agda
AGDALIB = lib/agda

doc/%.html: src/%.agda
	agda $< --html --html-dir=./doc/

%.agdai: %.agda
	agda $<

all: lib src/Readme.agdai

doc: lib doc/Readme.html

### libraries
lib: lib/agda/std-lib lib/stdlib++.agda

lib/stdlib++.agda:
	git clone -b 2.6 https://github.com/ElessarWebb/stdlib-plusplus.agda.git $(STDPP)

# checkout the compatible agda release source
lib/agda:
	git clone -b release-2.5.3 https://github.com/agda/agda/ $(AGDALIB)

# build the stdlib compatible with the agda release we're using
lib/agda/std-lib: lib/agda
	cd $(AGDALIB) && make fast-forward-std-lib

### cleaning
clean:
	find . -iname 'src/*.agdai' -exec rm {} \;

clean-all: clean
	rm -rf lib
