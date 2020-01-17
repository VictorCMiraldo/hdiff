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

runHDiff() {
  local path=$dataset/$1
  local parser=$2
  local exp=$3
  local name=${exp%%.*}
  local log="results/h-$name-$parser"

  meta "Running hdiff $name $parser"

  # hdiff
  for hh in 1 3 9; do
    for mm in nonest proper patience; do
      echo "Launching hdiff $parser $name $hh $mm"
       ./scripts/run-experiment.sh $dry -l "$log" -m 16 "$path" $exp \
          -h $hh -m $mm -p $parser 2> /dev/null &
    done
  done
}

runSTDiff() {
  local path=$dataset/$1
  local parser=$2
  local exp=$3
  local name=${exp%%.*}
  local log="results/st-$name-$parser"

  meta "Running stdiff $name $parser"

  # stdiff
  echo "Launching stdiff $parser $name"
  ./scripts/run-experiment.sh $dry -l "$log" -m 16 "$path" $exp \
    --stdiff -p $parser 2> /dev/null &
}

runSTMerge () {
  runSTDiff $1 $2 merge.sh
}

runHMerge () {
  runHDiff $1 $2 merge.sh
}

timeSTDiff () {
  runSTDiff $1 $2 diff.sh
}

timeHDiff () {
  runHDiff $1 $2 diff.sh
}

meta "Let the experiments begin"

#Runs stdiff on the supported languages
for lang in lua clj sh; do
  runSTMerge "conflicts-$lang" "$lang"
  timeSTDiff "conflicts-$lang" "$lang"
done
wait

#Runs hdiff on the supported languages
for lang in lua clj sh java; do
  runHMerge "conflicts-$lang" "$lang"
  wait
done

#Runs js and py with and without location information
for lang in js py; do
  runHMerge "conflicts-$lang" "$lang"
  runHMerge "conflicts-$lang" "$lang-loc"
  wait
done

#Runs all experiments with the dyck parser
for lang in lua clj sh js py; do
  runSTMerge "conflicts-$lang" "dyck"
  runSTMerge "conflicts-$lang" "dyck-loc"
done
wait

for lang in lua clj sh js py; do
  runHMerge "conflicts-$lang" "dyck"
  runHMerge "conflicts-$lang" "dyck-loc"
  wait
done

meta "We are done!"


