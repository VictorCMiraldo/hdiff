#!/bin/bash
set -uo pipefail

if [[ "$#" -lt "1" ]]; then
  echo "I need at least a directory!"
elif [[ ! -d "$1" ]]; then
  echo "'$1' is not a directory!"
fi
dir="$1"

shift

if [[ "$#" -lt "1" ]]; then
  max=$(ls -1 $dir | wc -l)
else
  max=$1
fi

timeout="5s"
mergetool="digem"

ver=$($mergetool --version)
echo "Running $mergetool at $ver for $max conflicts"

# limit to 8GiBs of memory per process
ulimit -v 8589934592

# TODO add timings

trap "exit" INT

for d in ${dir}/*; do
  if [[ "$max" -eq 0 ]]; then
    exit 0
  fi

  we_good=true
  names=("A" "O" "B")
  for fname in ${names[*]}; do
    if [[ ! -e "${d}/$fname.clj" ]]; then
      we_good=false
    fi
  done

  if $we_good; then
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
    max=$(( $max - 1 ))
  fi
done
