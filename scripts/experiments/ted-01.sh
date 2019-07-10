## This is not a standalone script; but meant to be passed to
## scripts/run-experiments.sh

## Process the arguments to this experiment uniformly
root="${BASH_SOURCE%/*}"
source "$root/process-arguments.sh"

if $showHeader; then
  echo "Location  FileA  FileB  cost  toEditScript.cost  GDiff.cost"
  exit 0
fi

function doOne () {
  a=$1
  b=$2

  n1=$(digem diff -q --cost --ted=Patch $a $b | cut -d':' -f 2 | paste -s -d' ')
  n2=$(timeout 8s digem gdiff -q $a $b        | cut -d':' -f 2)
  if [[ -z "$n2" ]]; then
    n2="timeout"
  fi
  echo "$prefix $(basename $a) $(basename $b) $n1 $n2"
}

doOne "$fo" "$fa"
sleep 1
doOne "$fo" "$fb"
sleep 1
doOne "$fa" "$fb"
