#! /bin/bash

for d in $(ls); do
  cd $d
  hdiff merge --test-merge M.* A.* O.* B.* >> /dev/null 2>&1
  res=$?
  case $res in
    2) echo "$d FAIL";;
    *) echo "$d OK($res)";;
  esac
  cd ..
done
