
TGT=index
LATEX=pdflatex -shell-escape -output-directory=dist

default : src/index.lhs src/body.lhs src/definitions.lhs src/stylish.lhs
	@mkdir -p dist
	lhs2TeX -o src/$(TGT).tex src/$(TGT).lhs
	./naming-convention src/body.lhs && \
	export TEXMFHOME=".:$(TEXMFHOME)" && \
	$(LATEX) src/$(TGT).tex 

dist/$(TGT).aux: default

bib: references.bib dist/$(TGT).aux
	bibtex dist/$(TGT).aux
	export TEXMFHOME=".:$(TEXMFHOME)" && \
	$(LATEX) src/$(TGT).tex

clean :
	cd dist && rm -rf * && cd ..
