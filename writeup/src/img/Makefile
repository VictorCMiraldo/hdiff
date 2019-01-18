SOURCES=$(wildcard *.svg)
TARGETS=$(SOURCES:.svg=.pdf)

all: $(TARGETS)

%.pdf: %.svg
	inkscape -A $@ $<
