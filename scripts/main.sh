#!/bin/bash
set -uo pipefail

root="${BASH_SOURCE%/*}"

# Make sure to cleanup if we kill this monster
trap "pkill -P $$; exit 1" SIGINT SIGTERM

if [[ "$#" -ne "1" ]]; then
  echo "usage: main.sh path/to/dataset"
  exit 1
fi
dataset="$1"

if [[ -d "results" ]]; then
  echo "Directory results already exists"
  exit 1
fi
mkdir results

dry="--dry"

meta () {
  echo "$(date) | $1" >> results/meta
}

## The merge experiment will
## run all variants of the merge algo over a single
## language.
runMerge() {
  local path=$dataset/$1
  local parser=$2
  local exp=merge.sh
  local name=${exp%%.*}
  local log="results/$name-$parser"

  for hh in 1 3 9; do
    for mm in nonest proper patience; do
      for kk in spine never always; do
        meta "Launching hdiff $parser $name $hh $mm $kk local"
        echo "Launching hdiff $parser $name $hh $mm $kk local"
         ./scripts/run-experiment.sh $dry \
            -l "$log.$hh.$mm.$kk.loc.log" -m 16 "$path" $exp \
            -m $hh -d $mm -o $kk -p $parser 2> /dev/null &
      done
    done
  done

  ## It is sensible to wait here; we have just launched 18
  ## jobs. Thanks jizo!
  wait

  for hh in 1 3 9; do
    for mm in nonest proper patience; do
      for kk in spine never always; do
        meta "Launching hdiff $parser $name $hh $mm $kk global"
        echo "Launching hdiff $parser $name $hh $mm $kk global"
         ./scripts/run-experiment.sh $dry \
            -l "$log.$hh.$mm.$kk.glob.log" -m 16 "$path" $exp \
            -m $hh -d $mm -o $kk -p $parser --skip-closures 2> /dev/null &
      done
    done
  done

  wait
}

runDiff () {
  local path=$dataset/$1
  local parser=$2
  local exp=diff.sh
  local name=${exp%%.*}
  local log="results/$name-$parser"

  for mm in nonest proper patience; do
      meta "Launching hdiff $parser $name $hh $mm $kk local"
      echo "Launching hdiff $parser $name $hh $mm $kk local"
       ./scripts/run-experiment.sh $dry \
          -l "$log.$hh.$mm.$kk.loc.log" -m 16 "$path" $exp \
          -d $mm -o never -p $parser 2> /dev/null &

      meta "Launching hdiff $parser $name $hh $mm $kk global"
      echo "Launching hdiff $parser $name $hh $mm $kk global"
      ./scripts/run-experiment.sh $dry \
         -l "$log.$hh.$mm.$kk.loc.log" -m 16 "$path" $exp \
         -d $mm -o never -p $parser --skip-closures 2> /dev/null &
  done
} 

meta "Let the experiments begin"

#Runs hdiff on the supported languages
for lang in lua clj sh java js py; do
  runMerge "conflicts-$lang" "$lang"
done

# Get timings for stdiff and hdiff
for lang in java lua clj; do
  runDiff "conflicts-$lang" "$lang"
done
wait

meta "We are done!"


