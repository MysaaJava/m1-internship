define extract
	cat $(1) | grep -A5000 -m1 $(3) | grep -B5000 -m1 $(4) | head -n -1 | sed 's/\\>\[6\]/\\>\[0\]/g' > $(2)
endef

all: report/build/M1Report.pdf

latex/FFOL.tex: FFOL.lagda
	agda --latex $<
	cp latex/agda.sty report/agda.sty
latex/FFOLInitial.tex: FFOLInitial.lagda
	agda --latex --allow-unsolved-metas $<
	cp latex/agda.sty report/agda.sty

report/build/M1Report.pdf: agda-tex-FFOL agda-tex-FIni
	$(cd report/; latexmk -pdf -xelatex -silent -shell-escape -outdir=build/ -synctex=1 "M1Report")

agda-tex-FIni: latex/FFOLInitial.tex
	mkdir -p report/agda
	@$(call extract,latex/FFOLInitial.tex,report/agda/ICont.tex,'Term\\ contexts\\ are\\ isomorphic\\ to\\ Nat','\\>\[0\]\\<')
	@$(call extract,latex/FFOLInitial.tex,report/agda/ITm.tex,'A\\ term\\ variable\\ is\\ a\\ de-bruijn','\\>\[0\]\\<')
	@$(call extract,latex/FFOLInitial.tex,report/agda/IFor.tex,'Now\\ we\\ can\\ define\\ formul','\\AgdaEmptyExtraSkip')
	@$(call extract,latex/FFOLInitial.tex,report/agda/ISubt.tex,'Then\\ we\\ define\\ term\\ substitutions','\\>\[0\]\\<')
	@$(call extract,latex/FFOLInitial.tex,report/agda/ISubtT.tex,'We\\ now\\ define\\ the\\ action\\ of\\ term\\ substitutions','\\>\[0\]\\<')
	@$(call extract,latex/FFOLInitial.tex,report/agda/ISubtF.tex,'We\\ can\\ now\\ subst\\ on\\ formul','\\AgdaEmptyExtraSkip')
	@$(call extract,latex/FFOLInitial.tex,report/agda/IIdCompT.tex,'We\\ now\\ can\\ define\\ identity\\ and\\ composition\\ of\\ term\\ substitutions','\\AgdaEmptyExtraSkip')
	@$(call extract,latex/FFOLInitial.tex,report/agda/IConp.tex,'We\\ can\\ now\\ define\\ proof\\ contexts','\\>\[0\]\\<')
	@$(call extract,latex/FFOLInitial.tex,report/agda/ISubtC.tex,'The\\ actions\\ of\\ Subt'"'"'s\\ is\\ extended\\ to\\ contexts','This\\ Conp\\ is\\ indeed\\ a\\ functor')
	@$(call extract,latex/FFOLInitial.tex,report/agda/IConpTp.tex,'We\\ can\\ also\\ add\\ a\\ term\\ that\\ will\\ not\\ be\\ used','We\\ show\\ how\\ it\\ interacts\\ with')
	@cat latex/FFOLInitial.tex | grep -A5000 -m1 'With\\ those\\ contexts,\\ we\\ have\\ everything\\ to\\ define\\ proofs' | grep -B5000 -m1 "AgdaEmptyExtraSkip" | head -n -1 | sed 's/\\>\[6\]/\\>\[0\]/g' > report/agda/IPf.tex
	@$(call extract,latex/FFOLInitial.tex,report/agda/IRen.tex,'We\\ now\\ can\\ create\\ Renamings','\\>\[0\]\\<')
	@$(call extract,latex/FFOLInitial.tex,report/agda/ISubp.tex,'But\\ we\\ need\\ something\\ stronger\\ than\\ just\\ renamings','They\\ are\\ indeed\\ stronger\\ than\\ renamings')
	@$(call extract,latex/FFOLInitial.tex,report/agda/ISubtP.tex,'\\>\[2\]\\AgdaOperator{\\AgdaFunction{\\AgdaUnderscore{}\[\\AgdaUnderscore{}\]pv','\\>\[0\]\\<')
	@$(call extract,latex/FFOLInitial.tex,report/agda/ISubtS.tex,'\\>\[2\]\\AgdaOperator{\\AgdaFunction{\\AgdaUnderscore{}\[\\AgdaUnderscore{}\]σ','\\AgdaEmptyExtraSkip')
	@$(call extract,latex/FFOLInitial.tex,report/agda/ISubpP.tex,'\\>\[2\]\\AgdaOperator{\\AgdaFunction{\\AgdaUnderscore{}\[\\AgdaUnderscore{}\]p}}','\\AgdaEmptyExtraSkip')
	@$(call extract,latex/FFOLInitial.tex,report/agda/IIdCompP.tex,'We\\ can\\ now\\ define\\ identity\\ and\\ composition\\ on\\ proof\\ substitutions','\\AgdaEmptyExtraSkip')
	@cat latex/FFOLInitial.tex | grep -A5000 -m1 'We\\ can\\ now\\ merge\\ the\\ two\\ notions\\ of\\ contexts,\\ substitutions,\\ and\\ everything' | grep -B5000 -m1 '\\>\[0\]\\<' > report/agda/ICon.tex
	@cat latex/FFOLInitial.tex | grep -A5000 -B1 -m1 '\\AgdaRecord{Sub}\\AgdaSpace{}%' | grep -B5000 -m1 '\\AgdaEmptyExtraSkip' > report/agda/ISub.tex
	@$(call extract,latex/FFOLInitial.tex,report/agda/IIdComp.tex,'(Con,Sub)\\ is\\ a\\ category\\ with\\ an\\ initial\\ object','\\>\[2\]\\AgdaFunction{idl}\\AgdaSpace{}')
	@$(call extract,latex/FFOLInitial.tex,report/agda/ICExt.tex,'We\\ have\\ our\\ two\\ context\\ extension\\ operators','\\AgdaEmptyExtraSkip')

agda-tex-FFOL: latex/FFOL.tex
	mkdir -p report/agda
	@$(call extract,latex/FFOL.tex,report/agda/Con.tex,'\\>\[6\]\\AgdaField{Con}',"AgdaEmptyExtraSkip")
	@$(call extract,latex/FFOL.tex,report/agda/Tm.tex,'\\>\[6\]\\AgdaField{Tm}',"AgdaEmptyExtraSkip")
	@$(call extract,latex/FFOL.tex,report/agda/Tm+.tex,'\\>\[6\]\\AgdaOperator{\\AgdaField{\\AgdaUnderscore{}▹ₜ}}',"AgdaEmptyExtraSkip")
	@$(call extract,latex/FFOL.tex,report/agda/For.tex,'\\>\[6\]\\AgdaField{For}',"AgdaEmptyExtraSkip")
	@$(call extract,latex/FFOL.tex,report/agda/Pf.tex,'\\>\[6\]\\AgdaOperator{\\AgdaField{\\AgdaUnderscore{}⊢\\AgdaUnderscore{}}}',"AgdaEmptyExtraSkip")
	@$(call extract,latex/FFOL.tex,report/agda/Pf+.tex,'\\>\[6\]\\AgdaOperator{\\AgdaField{\\AgdaUnderscore{}▹ₚ\\AgdaUnderscore{}}}',"AgdaEmptyExtraSkip")
	@$(call extract,latex/FFOL.tex,report/agda/R.tex,'\\>\[6\]\\AgdaField{R}',"AgdaEmptyExtraSkip")
	@$(call extract,latex/FFOL.tex,report/agda/Imp.tex,'\\>\[6\]\\AgdaOperator{\\AgdaField{\\AgdaUnderscore{}⇒\\AgdaUnderscore{}}}',"AgdaEmptyExtraSkip")
	@$(call extract,latex/FFOL.tex,report/agda/Forall.tex,'\\>\[6\]\\AgdaField{∀∀}',"AgdaEmptyExtraSkip")
	@$(call extract,latex/FFOL.tex,report/agda/LamApp.tex,'\\>\[6\]\\AgdaField{lam}',"AgdaEmptyExtraSkip")
	@$(call extract,latex/FFOL.tex,report/agda/ForallR.tex,'\\>\[6\]\\AgdaField{∀i}',"AgdaEmptyExtraSkip")

.PHONY: clean agda-tex agda-tex-FFOL
clean:
	rm -fr *.agdai report/agda latex report/build
