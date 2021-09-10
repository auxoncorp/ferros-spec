.PHONY: latex latex-clean latex-compile

latex: latex-compile latex-clean

latex-compile: latex-cnode latex-ut

latex-clean:
	find . -regextype egrep -regex ".*\.(aux|log|out|ptb)" | \
		xargs rm -f
	rm -rf latex/Ferros
	rm -rf latex/_minted-Base

latex-cnode:
	agda --latex Ferros/Resource/CNode/Base.lagda
	cd latex && \
	  	pdflatex --shell-escape Ferros/Resource/CNode/Base.tex
	mv latex/Base.pdf pdf/cnode-allocation.pdf

latex-ut:
	agda --latex Ferros/Resource/Untyped/Base.lagda
	cd latex && \
	  	pdflatex --shell-escape Ferros/Resource/Untyped/Base.tex
	mv latex/Base.pdf pdf/untyped-allocation.pdf
