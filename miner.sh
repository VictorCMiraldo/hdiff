#!/bin/bash
set -uo pipefail

if [[ "$#" -ne "1" ]]; then
  echo "I need a directory!"
elif [[ ! -d "$1" ]]; then
  echo "'$1' is not a directory!"
fi

dir="$1"
timeout="5s"
mergetool="digem"

ver=$($mergetool --version)
echo "Running $mergetool at $ver"

# limit to 8GiBs of memory per process
ulimit -v 8589934592

# TODO add timings

trap "exit" INT

for d in ${dir}/*; do
  timeout "${timeout}" "${mergetool}" merge "${d}/A.clj" "${d}/O.clj" "${d}/B.clj"
  res=$?
  case $res in
    0) echo "${d} $mergetool success" ;;
    1) echo "${d} $mergetool conflicting" ;;
    2) echo "${d} $mergetool panic"
       mkdir -p PANIC 
       cp "${d}/A.clj" PANIC/
       cp "${d}/O.clj" PANIC/
       cp "${d}/B.clj" PANIC/
      exit 2
    ;;
    *) echo "${d} $mergetool unknown($res)" ;;
  esac
done
