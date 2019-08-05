
default:slides.pdf

verbose:slides.md
	pandoc -t beamer slides.md -o ../dist/slides.pdf\
	  --slide-level=2\
	  --pdf-engine=xelatex\
	  --verbose\
	  --template uu-metropolis/beamer-template.tex


slides.pdf: slides.md
	pandoc -t beamer slides.md -o ../dist/slides.pdf\
	  --slide-level=2\
	  --pdf-engine=xelatex\
	  --template uu-metropolis/beamer-template.tex

tex: slides.md
	pandoc -t beamer slides.md -o ../dist/slides.tex\
	  --slide-level=2\
	  --pdf-engine=xelatex\
	  --verbose\
	  --template uu-metropolis/beamer-template.tex

clean:
	rm *.aux *.log *.nav *.out *.snm *.toc *.vrb
