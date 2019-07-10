#!/bin/bash
set -uo pipefail

pushd () {
    command pushd "$@" > /dev/null
}

popd () {
    command popd "$@" > /dev/null
}

function showUsage() {
  echo "usage: ./run-experiment.sh path/to/dataset rest-of-args go-to-experiment"
  echo "  Runs '\$\@' over the specified dataset, once per folder."
  echo "  for the A, O , B found within the current foler."
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
  echo "  run-experiment.sh will exit if its specified experiment returns ExitFailure"
  echo "  it is advised to make a separate script for each experiment that handles logging and the likes"
  echo ""
  echo "  Example usage:"
  echo ""
  echo "    ./run-experiment.sh dataset/conflicts-el digem merge A.el O.el B.el"
  echo ""
  echo "      Will run digem merge on all conflicts within dataset/conflicts-el."
  echo "      Better yet would be to write a script 'merge-experiment.sh' and pass it instead:"
  echo "        ./run-experiment.sh dataset/conflicts-el ./scripts/merge-experiment.sh"
  echo ""
  exit 0
}

if [[ "$#" -lt "1" ]]; then
  showUsage
fi

while [[ "$1" == -* ]]; do
  arg=$1;
  shift;
  case $arg in
    -h|--help) showUsage ;;
    *)         showUsage ;;
  esac
done

dir="$1"
shift

if [[ ! -d "$dir" ]]; then
  echo "'$dir' is not a directory!"
  showUsage
fi

# limit to 8GiBs of memory per process
ulimit -v 8589934592

trap "exit" INT

for d in ${dir}/*; do
  fa=$(find "${d}" -name "A.*")
  fo=$(find "${d}" -name "O.*")
  fb=$(find "${d}" -name "B.*")
  if [[ -z "$fa" ]] || [[ -z "$fb" ]] || [[ -z "$fo" ]]; then
    echo "!!! ${d} !!! Wrong structure; some files not found" >> run-experiment-errors.log
    continue
  else
    ## Everything was found alright, we jump in there and
    ## run whatever experiment we want.
    pushd ${d}
    $@
    if [[ "$?" -ne "0" ]]; then
      exit 1
    fi
    popd
  fi
done
      
