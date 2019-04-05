.PHONY: latex latex-clean latex-compile

latex: latex-compile latex-clean

latex-compile:
	agda --latex Ferros/Resource/CNode/Base.lagda
	cd latex && \
	  	pdflatex --shell-escape Ferros/Resource/CNode/Base.tex
	mv latex/Base.pdf latex/cnode-allocation.pdf

latex-clean:
	find . -regextype egrep -regex ".*\.(aux|log|out|ptb)" | \
		xargs rm -f
	rm -rf latex/Ferros
	rm -rf latex/_minted-Base
