## This is not a standalone script; but meant to be passed to
## scripts/run-experiments.sh


## Process the arguments to this experiment uniformly
root="${BASH_SOURCE%/*}"
source "$root/process-arguments.sh"

if $showHeader; then
  echo "Location  MergeResult"
  exit 0
fi

timeout="5s"

timeout "${timeout}" digem merge "$fa" "$fo" "$fb"
res=$?
case $res in
  0) echo "$prefix success"               ;;
  1) echo "$prefix conflicting"           ;;
  2) echo "$prefix panic";         exit 1 ;;
  *) echo "$prefix unknown($res)"; exit 1 ;;
esac

