## This file is meant to be included as the first instruction
## in all experiments; it process the command line arugments in a uniform fashion.
set -uo pipefail

prefix=""
showHeader=false
fa=""
fb=""
fo=""

while [[ "$#" -gt 0 ]]; do
  arg=$1;
  shift;
  case $arg in
    --header) showHeader=true; break ;;
    --prefix) prefix=$1; shift ;;
    --fa) fa=$1; shift ;;
    --fb) fb=$1; shift ;;
    --fo) fo=$1; shift ;;
    *) echo "Unknown argument"; exit 1 ;;
  esac
done

# limit to 8GiBs of memory per process
ulimit -v 8589934592

