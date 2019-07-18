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

timeout="5s"

timeout "${timeout}" digem merge -h $height "$fa" "$fo" "$fb"
res=$?
case $res in
  0) echo "$prefix $height success"               ;;
  1) echo "$prefix $height conflicting"           ;;
  2) echo "$prefix $height panic";         exit 1 ;;
  *) echo "$prefix $height unknown($res)"; exit 1 ;;
esac

