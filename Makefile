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
html/%.html: %.lagda
	agda --html --allow-unsolved-metas $<
html/%.html: %.agda
	agda --html --allow-unsolved-metas $<

report/build/M1Report.pdf: agda-tex agda-html report/M1Report.tex report/header.tex report/Bilibibio.bib
	cd report/; latexmk -pdf -xelatex -silent -shell-escape -outdir=build/ -synctex=1 "M1Report"

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

agda-html: report/CodeIndex.html html/PropUtil.html html/ListUtil.html html/ZOL2.html html/ZOLInitial.html html/ZOLCompleteness.html html/IFOL2.html html/IFOLInitial.html html/IFOLCompleteness.html html/FFOL.html html/FFOLInitial.html
	mkdir -p html/
	cp report/CodeIndex.html html/
	cd html; ebook-convert CodeIndex.html Code.pdf --base-font-size=8 --margin-bottom=3 --margin-top=3 --paper-size=a4 --language=en --authors="Samy Avrillon" --toc-filter=".*"

.PHONY: clean agda-tex agda-tex-FFOL agda-tex-ZOL agda-tex-FIni
clean:
	rm -fr *.agdai report/agda latex report/build html html2
