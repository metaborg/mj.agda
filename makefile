
%.agdai: %.agda
	agda $<

all: Readme.agdai

clean:
	find . -iname '*.agdai' -exec rm {} \;
