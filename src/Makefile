.PHONY: minisail clean

all: minisail

minisail:
	dune build --profile release main.exe
	cp _build/default/main.exe minisail

clean:
	-dune clean
