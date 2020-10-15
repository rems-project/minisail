.PHONY: minisail clean

OTT=ott
SAIL_OTT=~/github/sail/language/sail.ott

all: minisail

sail_pp.ml : $(SAIL_OTT)
	$(OTT) $(SAIL_OTT) -ocaml_pp sail_pp.ml
	python fixup_sail_pp.py sail_pp.ml

minisail: 
	dune build --profile release main.exe
	cp _build/default/main.exe minisail

clean:
	-dune clean
