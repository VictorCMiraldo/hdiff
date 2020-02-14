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
mode="nonest"
parser=""
stdiff=false
while [[ "$#" -gt 0 ]]; do
  arg=$1;
  shift;
  case $arg in
    -h|--height) height=$1; shift;;
    -m|--mode)   mode=$1; shift;;
    -p|--parser) parser=$1; shift;;
    -s|--stdiff) stdiff=true;;
    *) echo "Unknown experiment argument: $arg"; exit 1 ;;
  esac
done

timeout="45s"
function doMerge() {
  local hdr=""
  local res=42
  if $stdiff; then
    hdr="$prefix _ stdiff"
    timeout "${timeout}" stdiff -p $parser merge --test-merge "$fm" "$fa" "$fo" "$fb"
    res=$?
  else
    hdr="$prefix $height $mode"
    timeout "${timeout}" hdiff -p $parser merge -d $mode -m $height --test-merge "$fm" "$fa" "$fo" "$fb"
    res=$?
  fi
  case $res in
    0)   output "$hdr success"       ;;
    1)   output "$hdr conflicting"   ;;
    2)   output "$hdr apply-fail"    ;;
    3)   output "$hdr merge-diff"    ;;
    10)  output "$hdr parse-error"   ;;
    124) output "$hdr timeout"       ;;
    *)   output "$hdr unknown($res)" ;;
  esac
}

echo "[$$]: Running at $prefix"
doMerge 
