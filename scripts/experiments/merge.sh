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
globscope=""
parser=""
while [[ "$#" -gt 0 ]]; do
  arg=$1;
  shift;
  case $arg in
    -m|--min-height)   height=$1; shift;;
    -d|--diff-mode)    mode=$1; shift;;
    -p|--parser)       parser=$1; shift;;
    --global-scope)    globscope="--global-scope";;
    *) echo "Unknown experiment argument: $arg"; exit 1 ;;
  esac
done

timeout="45s"
function doMerge() {
  local hdr=""
  local res=42
  hdr="$prefix $height $mode"
  if [[ ! -z "$skipclosures" ]]; then 
    hdr="$hdr global"
  else
    hdr="$hdr local"
  fi
  timeout "${timeout}" hdiff -p $parser \
    merge -d $mode -m $height $skipclosures \
    --test-merge "$fm" "$fa" "$fo" "$fb"
  res=$?
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
