define extract
	cat $(1) | grep -A5000 -m1 $(3) | grep -B5000 -m1 $(4) | head -n -1 | sed 's/\\>\[6\]/\\>\[0\]/g' > $(2)
endef

define split
	last=-1;i=1;for cur in $$(grep -n -e "--\\\\#" $(1) | cut -d':' -f1); do if [ ! "-1" -eq $$last ]; then dif=$$((cur-last-1));cat $(1) | head -n $$((cur-2)) | tail -n $$((dif)) | awk -f stripAgda.awk > $(2)$$i$(3); i=$$((i+1)); fi; last=$$cur; done
endef

all: report/build/M1Report.pdf

latex/%.tex: %.lagda
	agda --latex --allow-unsolved-metas $<
	cp latex/agda.sty report/agda.sty

report/build/M1Report.pdf: agda-tex-FFOL agda-tex-FIni agda-tex-ZOL
	$(cd report/; latexmk -pdf -xelatex -silent -shell-escape -outdir=build/ -synctex=1 "M1Report")

agda-tex: latex/ZOL2.tex latex/ZOLInitial.tex latex/ZOLCompleteness.tex latex/IFOL2.tex latex/IFOLInitial.tex latex/IFOLInitial.tex latex/FFOL.tex latex/FFOLInitial.tex
	mkdir -p report/agda
	$(call split,"latex/ZOL2.tex","report/agda/ZOL-",".tex")
	$(call split,"latex/ZOLInitial.tex","report/agda/ZOL-I-",".tex")
	$(call split,"latex/ZOLCompleteness.tex","report/agda/ZOL-U-",".tex")
	$(call split,"latex/IFOL2.tex","report/agda/IFOL-",".tex")
	$(call split,"latex/IFOLInitial.tex","report/agda/IFOL-I-",".tex")
	$(call split,"latex/IFOLCompleteness.tex","report/agda/IFOL-C-",".tex")
	$(call split,"latex/FFOL.tex","report/agda/FFOL-",".tex")
	$(call split,"latex/FFOLInitial.tex","report/agda/FFOL-I-",".tex")

.PHONY: clean agda-tex agda-tex-FFOL agda-tex-ZOL agda-tex-FIni
clean:
	rm -fr *.agdai report/agda latex report/build
