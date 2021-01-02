ISA_ROOT=/local/scratch/mpew2/Isabelle
ISA_ROOT=/cygdrive/e/Software/Isabelle


all:	docs

# To force a rebuild you might need to delete the MiniSail.db in
# /cygdrive/c/Users/User/.isabelle/Isabelle2020/heaps/polyml-5.8.1_x86_64_32-windows/log



docs:
	$(ISA_ROOT)/Isabelle2020/bin/isabelle build -D . -o browser_info -v MiniSail


snippets:
	$(ISA_ROOT)/Isabelle2020/bin/isabelle build -D . Snippets

