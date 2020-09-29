##

# Targets
#
# Standalone documents:
#   minisail_anf.pdf  - MiniSailAnf grammar and rules
#   sail_to_anf.pdf  - Sail to MiniSail conversion
#   sail_decl_rules.pdf  - Sail declarative type checking rules
#

OTT=~/github/ott_markw/bin/ott 
#OTT=~/github/ott/bin/ott -signal_parse_errors true
OTT_MASTER=$(OTT)
#ott -signal_parse_errors true
SAILDIR=~/github/sail_minisail
SAILOTT=$(SAILDIR)/language/sail.ott

all: minisail_anf.pdf  minisail_anf_include.tex ms_to_anf_include.tex sail_to_ms_include.tex minisailplus_include.tex

%.pdf : %.tex
	pdflatex $<

##
## MiniSail ANF
##

minisail_anf_b.ott : minisail_anf.ott
	sed -e 's/\(\(%[^%]\)*\)%b/\1/' minisail_anf.ott > minisail_anf_b.ott

minisail_anf.tex:   common_metavar.ott minisail_anf_b.ott
	$(OTT) -merge true -sort false -generate_aux_rules false -picky_multiple_parses false -o $@  common_metavar.ott minisail_anf_b.ott
	python fixup_tex.py $@

# Exclude superscripts on metavars
minisail_anf_include.tex: common_metavar.ott minisail_anf_b.ott
	$(OTT) -tex_name_prefix anf -tex_wrap false -merge true -sort false -generate_aux_rules false -picky_multiple_parses false -o $@  common_metavar.ott minisail_anf_b.ott
	cp $@ ~/sharemnt

##
## Conversion from Sail to ANF
##

minisail_anf_a.ott : minisail_anf.ott
	sed -e 's/\(\(%[^%]\)*\)%a/\1/' minisail_anf.ott > minisail_anf_a.ott


SAILTOANF=$(SAILOTT) sail_to_anf_metavar.ott minisail_anf_b.ott sail_to_anf.ott

sail_to_anf.tex: $(SAILTOANF)
	$(OTT_MASTER)  -sort false -generate_aux_rules false -merge true -o $@ -picky_multiple_parses false $^

sail_to_anf_include.tex: $(SAILTOANF)
	$(OTT_MASTER) -tex_name_prefix stoanf -sort false -tex_wrap false -generate_aux_rules false -merge true -o $@ -picky_multiple_parses false $^
	sed -i 's/\ott/\stoanf/g' $@



##
## Sail declarative rules
##


sail_decl_rules.tex : $(SAILOTT) sail_decl_rules.ott
		$(OTT) -sort false -merge true -o $@ $^

sail_decl_rules_include.tex : $(SAILOTT) sail_decl_rules.ott
		$(OTT) -tex_name_prefix sc -tex_wrap false -sort false -merge true -o $@ $^
		sed -i 's/\ott/\sc/g' $@


##
## Sail grammar
##

sail_include.tex : $(SAILOTT)
	$(OTT_MASTER) -tex_name_prefix sail -sort false -tex_wrap false -generate_aux_rules false -merge true -o $@ -picky_multiple_parses false $^
	sed -i 's/\ott/\sail/g' sail_include.tex

sail.tex : $(SAILOTT)
	$(OTT_MASTER) -sort false -generate_aux_rules false -merge true -o $@ -picky_multiple_parses false $^
	sed -i 's/\ott/\sail/g' sail_include.tex


