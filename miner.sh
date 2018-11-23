#!/bin/bash
set -uo pipefail

timeout="5s"
mergetool="digem"
lang="clj"
skip=0
exitonconflict=false
logfile=""

function showUsage() {
  echo "usage: ./miner.sh [options] path/to/dataset"
  echo "  Mines a folder for conflicts using '$mergetool'"
  echo "  The 'dataset' folder must have the following structure:"
  echo ""
  echo "   $ tree path/to/dataset"
  echo "     dataset"
  echo "     ├── folder1"
  echo "     │   ├── A.lang"
  echo "     │   ├── B.lang"
  echo "     │   └── O.lang"
  echo "     ├── folder2"
  echo "     │   ├── A.lang"
  echo "     │   ├── B.lang"
  echo "     │   └── O.lang"
  echo "     ."
  echo "     ."
  echo "     ."
  echo ""
  echo "  Options are:"
  echo ""
  echo "    -s , --skip INT"
  echo "      Will skip the 'n' first folders"
  echo ""
  echo "    -l , --lang $lang | while | lua | ..."
  echo "      Select the language we are supposed to merge"
  echo "      Default: $lang"
  echo ""
  echo "    -x , --exit-on-conflict"
  echo "      Stops the script on the first true conflict or on 'panic'"
  echo ""
  echo "    -o , --log-file FILE"
  echo "      Keeps a log in a given file, if specified"
  echo ""
  exit 0
}

if [[ "$#" -lt "1" ]]; then
  showUsage
fi

while [[ "$#" -gt "1" ]]; do
  arg=$1;
  shift;
  case $arg in
    -s|--skip) skip="${1?'missing argument to --skip'}" ; shift ;;
    -l|--lang) lang="${1?'missing argument to --lang'}" ; shift ;;
    -o|--log-file) logfile="${1?'missing argument to --log-file'}" ; shift ;;
    -x|--exit-on-conflict) exitonconflict=true ;;
  esac
done

if [[ ! -d "$1" ]]; then
  echo "'$1' is not a directory!"
  showUsage
fi

if [[ -e "$logfile" ]]; then
  echo "Log file exists, please rename or choose another one."
  echo " !! abborting"
  exit 1
fi

dir="$1"

ver=$($mergetool --version)
echo "Running $mergetool at $ver for conflicts"

# limit to 8GiBs of memory per process
ulimit -v 8589934592

# TODO add timings

trap "exit" INT

for d in ${dir}/*; do
  if [[ "$skip" -gt 0 ]]; then 
    skip=$(( $skip - 1 ));
    echo "${d} skip"
  else
    if [[ ! -f "${d}/A.$lang" ]] || [[ ! -f "${d}/B.$lang" ]] || [[ ! -f "${d}/O.$lang" ]]; then
      echo "${d} $mergetool file-not-found" | tee -a $logfile 
      continue
    fi

    timeout "${timeout}" "${mergetool}" merge "${d}/A.$lang" "${d}/O.$lang" "${d}/B.$lang"
    res=$?
    case $res in
      0) echo "${d} $mergetool success" | tee -a $logfile ;;
      1) echo "${d} $mergetool conflicting" | tee -a $logfile
         if $exitonconflict && [[ ! -e "$d/true-conflict" ]]; then
           mkdir -p PANIC      
           cp "${d}/A.$lang" PANIC/
           cp "${d}/O.$lang" PANIC/
           cp "${d}/B.$lang" PANIC/
           exit 1
         fi 
      ;;
      2) echo "${d} $mergetool panic" | tee -a $logfile
         if $exitonconflict; then
           mkdir -p PANIC 
           cp "${d}/A.$lang" PANIC/
           cp "${d}/O.$lang" PANIC/
           cp "${d}/B.$lang" PANIC/
           exit 2
         fi
      ;;
      *) echo "${d} $mergetool unknown($res)" | tee -a $logfile ;;
    esac
  fi
done
