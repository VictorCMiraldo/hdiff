
TGT=index
LATEX=pdflatex -shell-escape -output-directory=dist

default : src/index.lhs src/body.lhs src/definitions.lhs src/stylish.lhs
	make -C src/img
	@mkdir -p dist
	lhs2TeX -o src/$(TGT).tex src/$(TGT).lhs
	./naming-convention src/body.lhs && \
	export TEXMFHOME=".:$(TEXMFHOME)" && \
	$(LATEX) src/$(TGT).tex 

nolhs: src/$(TGT).tex
	export TEXMFHOME=".:$(TEXMFHOME)" && \
	$(LATEX) src/$(TGT).tex 

dist/$(TGT).aux: default

camerardy: bib default
	rm -rf camera-rdy/ && \
	mkdir camera-rdy && \
	cp acmart/acmart.cls camera-rdy/ && \
	cp acmart/ACM-Reference-Format.bst camera-rdy/ && \
	cp src/index.tex camera-rdy/ && \
	cp references.bib camera-rdy/ && \
	cp -R src/img camera-rdy/ && \
	cd camera-rdy && zip -r camera-rdy.zip *

bib: references.bib dist/$(TGT).aux
	bibtex dist/$(TGT).aux
	export TEXMFHOME=".:$(TEXMFHOME)" && \
	$(LATEX) src/$(TGT).tex

clean :
	cd dist && rm -rf * && cd ..

