#!/bin/bash
set -uo pipefail

difftool="digem"
lang="lua"
logfile=""

function showUsage() {
  echo "usage: ./getstats.sh [options] path/to/dataset"
  echo "  Diffs the original file to its 'A' modification using '$difftool'"
  echo "  and displays statistics about it"
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
  echo "    -l , --lang clj | while | lua | ..."
  echo "      Select the language we are supposed to merge"
  echo "      Default: $lang"
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
    -l|--lang) lang="${1?'missing argument to --lang'}" ; shift ;;
    -o|--log-file) logfile="${1?'missing argument to --log-file'}" ; shift ;;
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

ver=$($difftool --version)
echo "Running $difftool at $ver for statistics"

echo "directory; filesize O; filesize A; astsize O; astsize A; digem patch size; time; diff patch size;" | tee -a $logfile

for d in ${dir}/*; do
  if [[ ! -f "${d}/A.$lang" ]] || [[ ! -f "${d}/O.$lang" ]]; then
    echo "${d} $difftool file-not-found" | tee -a $logfile 
    continue
  fi

  line=$(${difftool} diff -s "${d}/O.$lang" "${d}/A.$lang")
  res=$?
  if [[ $res == "0" ]]; then
    sizeo=$(stat --printf="%s" "${d}/O.$lang") 
    sizea=$(stat --printf="%s" "${d}/A.$lang") 
    diff "${d}/O.$lang" "${d}/A.$lang" > tmpdifffile
    sizediff=$(stat --printf="%s" tmpdifffile)
    echo "$d $sizeo $sizea $line $sizediff" | tee -a $logfile
  else
    echo "${d} error"
  fi
done

