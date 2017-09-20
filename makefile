# some library paths
STDPP = lib/stdlib++.agda
AGDALIB = lib/agda

%.agdai: %.agda
	agda $<

all: src/Readme.agdai

# checkout the required library versions locally
lib:
	git clone -b release-2.5.3 https://github.com/agda/agda/ $(AGDALIB)
	cd $(AGDALIB) && make fast-forward-std-lib
	git clone -b 2.6 git@github.com:ElessarWebb/stdlib-plusplus.agda.git $(STDPP)

clean:
	find . -iname 'src/*.agdai' -exec rm {} \;
