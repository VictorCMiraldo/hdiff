## This is not a standalone script; but meant to be passed to
## scripts/run-experiments.sh


## Process the arguments to this experiment uniformly
root="${BASH_SOURCE%/*}"
source "$root/process-arguments.sh"

if $showHeader; then
  echo "Location  MinSharingHeight  MergeResult"
  exit 0
fi

#######################
## Actual experiment ##


height=1
while [[ "$#" -gt 0 ]]; do
  arg=$1;
  shift;
  case $arg in
    -h|--height) height=$1; shift;;
    *) echo "Unknown experiment argument: $arg"; exit 1 ;;
  esac
done

timeout="7s"
function doMerge() {
  local mode=$1
  local h=$2
  timeout "${timeout}" hdiff merge -d $mode -m $h "$fa" "$fo" "$fb"
  res=$?
  case $res in
    0)  echo "$prefix $h $mode success"               ;;
    1)  echo "$prefix $h $mode conflicting"           ;;
    2)  echo "$prefix $h $mode panic";         exit 1 ;;
    10) echo "$prefix $h $mode parse-error"           ;;
    *)  echo "$prefix $h $mode unknown($res)"         ;;
  esac
}

doMerge "proper" 1
doMerge "proper" 2
doMerge "proper" 3
doMerge "proper" 4
doMerge "nonest" 1
doMerge "nonest" 4
# doMerge "patience"
