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

res="res-$(git log -n 1 --format=%h)"
if [[ -d $res ]]; then
  echo "Directory res already exists"
  exit 1
fi

mkdir -p $res/individual

dry="--dry"

meta () {
  echo "$(date) | $1" >> $res/meta
}

## The merge experiment will
## run all variants of the merge algo over a single
## language.
runMergeLoc() {
  local path=$dataset/$1
  local parser=$2
  local exp=merge.sh
  local name=${exp%%.*}
  local log="$res/individual/$name-$parser"

  for hh in 1 6; do
    for mm in nonest proper patience; do
        meta "Launching hdiff $parser $name $hh $mm local"
        echo "Launching hdiff $parser $name $hh $mm local"
         ./scripts/run-experiment.sh $dry \
            -l "$log.$hh.$mm.loc.log" -m 16 "$path" $exp \
            -m $hh -d $mm -p $parser 2> /dev/null &
    done
  done
}

runMergeGlob() {
  local path=$dataset/$1
  local parser=$2
  local exp=merge.sh
  local name=${exp%%.*}
  local log="$res/individual/$name-$parser"

  for hh in 1 6; do
    for mm in nonest proper patience; do
        meta "Launching hdiff $parser $name $hh $mm global"
        echo "Launching hdiff $parser $name $hh $mm global"
         ./scripts/run-experiment.sh $dry \
            -l "$log.$hh.$mm.glob.log" -m 16 "$path" $exp \
            -m $hh -d $mm -p $parser --global-scope 2> /dev/null &
      done
    done
  done
}

runDiff () {
  local path=$dataset/$1
  local parser=$2
  local exp=diff.sh
  local name=${exp%%.*}
  local log="$res/individual/$name-$parser"

  for mm in nonest proper patience; do
      meta "Launching hdiff $parser $name $hh $mm local"
      echo "Launching hdiff $parser $name $hh $mm local"
       ./scripts/run-experiment.sh $dry \
          -l "$log.1.$mm.loc.log" -m 16 "$path" $exp \
          -d $mm -o never -p $parser 2> /dev/null &
  done
} 

meta "Let the experiments begin"

#Runs hdiff on the supported languages
for lang in lua clj sh java js py; do
  runMergeLoc  "conflicts-$lang" "$lang"
  runMergeGlob "conflicts-$lang" "$lang"
  wait
done

# Get timings for stdiff and hdiff
for lang in java lua clj; do
  runDiff "conflicts-$lang" "$lang"
done
wait

meta "We are done!"

for lang in java js lua py clj sh; do 
  ./scripts/process-merge-results.sh $res/individual/merge-$lang.* | sort -nr -k6 > $res/$lang-summary
done

for lang in java js lua py clj sh; do 
  echo "## $lang" >> final
  head -n 3 $res/$lang-summary >> final
done

