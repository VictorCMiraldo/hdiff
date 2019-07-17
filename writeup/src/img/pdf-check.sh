#! /bin/bash
for i in *pdf; do
  echo;
  echo $i;
  gs -sDEVICE=pdfwrite -dBATCH -dNOPAUSE -dNOPROMPT -dPDFSETTINGS=/prepress -sOutputFile=RES -f $i;
done

rm RES
