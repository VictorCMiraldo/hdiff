#!/bin/bash
set -uo pipefail

root="${BASH_SOURCE%/*}"

memlim=8
interval=1
verbose=false
logfile=""
dry=false

function showUsage() {
  echo "usage: ./run-experiment.sh [options] path/to/dataset rest-of-args go-to-experiment"
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
  echo "  it is advised to make a separate script for each experiment that handles "
  echo "  logging and the likes"
  echo ""
  echo "  Options:"
  echo ""
  echo "   -s , --sleep INT"
  echo "    sleeps for n seconds between experiments, defaults to $interval s"
  echo "    This is useful when running experiments over a large amount of time."
  echo "    Sleeping in between calls to the experiment script gives the computer some"
  echo "    time to cool off"
  echo ""
  echo "  -m , --memlim gigs"
  echo "    How many gigabytes of memory do we allow the experiment to use."
  echo "    Passed to 'ulimit -v \$(( gigs * 1024 * 1024 ))'."
  echo "    Defaults to: $memlim"
  echo ""
  echo "  -l logfile"
  echo "    Logs to logfile"
  echo
  echo "  --dry"
  echo "    Only runs on the first datapoint"
  echo ""
  echo "  Example usage:"
  echo ""
  echo "    ./run-experiment.sh dataset/conflicts-el hdiff merge A.el O.el B.el | tee LOG"
  echo ""
  echo "      Will run hdiff merge on all conflicts within dataset/conflicts-el."
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
    -s|--sleep) interval=$1; shift ;;
    -m|--memlim) memlim=$1; shift ;;
    --dry) dry=true;;
    -l) logfile=$1; shift;;
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

exp="$root/experiments/$1"
shift

if [[ ! -f "$exp" ]]; then
  echo "Please specify an existing experiment!"
  echo "I can't find '$exp'"
  showUsage
fi

trap "exit" SIGINT SIGTERM

# limit the memory usage
ulimit -v $(( $memlim * 1024 * 1024 ))

# ver=$(hdiff --version)
# echo "[run-experiment; $ver]"

for d in ${dir}/*; do
  sleep "$interval"
  fa=$(find "${d}" -name "A.*")
  fo=$(find "${d}" -name "O.*")
  fb=$(find "${d}" -name "B.*")
  fm=$(find "${d}" -name "M.*")
  if [[ -z "$fa" ]] || [[ -z "$fb" ]] || [[ -z "$fo" ]] || [[ -z "$fm" ]]; then
    echo "!!! ${d} !!! Wrong structure; some files not found" >> run-experiment-errors.log
    continue
  else
    ## Everything was found alright, we jump in there and
    ## run whatever experiment we want.
    $exp --log "$logfile" --prefix "$(basename ${d})" --fa "$fa" --fb "$fb" --fo "$fo" --fm "$fm" --rest $@
    ecode=$?
    if [[ "$ecode" -ne "0" ]]; then
      echo "!!! ${d} !!! Experiment Returned $ecode" >> run-experiment-errors.log
    fi
  fi
  if $dry; then break; fi
done
 
