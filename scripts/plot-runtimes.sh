#! /bin/bash
set -euo pipefail

showUsage () {
  echo "./scripts/plot-runtimes.sh [options] [files]"
  echo ""
  echo "  Plots the aggregated runtime versus the ast size"
  echo "of the specified files, which should have been produced"
  echo "by ./scripts/run-experiment.sh diff.sh; they have the following"
  echo "format:"
  echo ""
  echo "..."
  echo "some-conflict-0afe13-4315a42 h mode time(s):float n+m:int cost:int [cost(es):int]"
  echo "..."
  echo "  "
  echo "  Supported options are:"
  echo ""
  echo "  -M | --maxsize int"
  echo "    Only considers entries with 'n+m' of at most maxsize."
  echo "    A value of 0 means infinity here."
  echo ""
  echo "  -m | --minsize int"
  echo "    Only considers entries with 'n+m' of at least minsize."
  echo ""
  echo "  -o | --outfile fname"
  echo "    Outputs the produced svg to the specified file"
  echo ""
}

if [[ "$#" -eq 0 ]]; then
  showUsage
  exit 1
fi

minsize=0
maxsize=0 # maxsize = 0 means infinity
outfile="plot.svg"
title="Graph title"
while [[ "$1" == -* ]]; do
  arg=$1;
  shift;
  case $arg in
    -M|--maxsize) maxsize=$1; shift ;;
    -m|--minsize) minsize=$1; shift ;;
    -o|--outfile) outfile=$1; shift ;;
    --title) title=$1; shift ;;
    -h|--help) showUsage ;;
    *)         showUsage ;;
  esac
done

# Create a temporary file to filter out columns and feed to gnuplot
aux=$(tempfile)

if [[ "$maxsize" -gt 0 ]]; then
  awks=" { if ($minsize <= \$2 && \$2 <= $maxsize) print \$2 \" \" \$1 } "
else
  awks=" { if ($minsize <= \$2) print \$2 \" \" \$1 } "
fi

for f in $@; do
  if [[ ! -f "$f" ]]; then
    echo "file '$f' does not exist; aborting"
    exit 1
  fi

  cat "$f" | cut -d' ' -f4,5 | sed 's/\(time(s)\|n+m\)://g' | awk "$awks" >> $aux
done

# http://triclinic.org/2015/04/publication-quality-plots-with-gnuplot/
gnuplot <<GNUPLOTSCRIPT
set terminal svg enhanced size 500,500
set output '$outfile'
set title  '$title'
set encoding iso_8859_1
set xlabel 'AST Size (n + m)'
set ylabel 'Time (s)'
set nokey
set grid
# set xrange [0:10]
# set yrange [0:1000]
set format x "%2.0t{/Symbol \327}10^{%L}"
plot '$aux' w p lc 6
GNUPLOTSCRIPT

# cleanup our tempfile
rm $aux
