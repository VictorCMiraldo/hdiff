## This file is meant to be included as the first instruction
## in all experiments; it process the command line arugments in a uniform fashion.
set -uo pipefail

function showHelpPA() {
  echo "Options available to experiments are:"
  echo ""
  echo " --header"
  echo "   Displays a header with column labels; helpful for parsing the output later."
  echo ""
  echo " --prefix <path>"
  echo "   Prefixes the output with this prefix"
  echo ""
  echo " --fa path, --fb path, --fo path, --fm path"
  echo "   Which are the files being processed."
  echo ""
  echo " --rest"
  echo "   Identifies the start of user supplied arguments."
  echo ""
  echo " --memlimit kbytes"
  echo "   Argument to 'ulimit -v'; limiting how much memory we allow ourselves to use"
  echo "   Defaults to $memlim (8 GiBs)"
  echo ""
  echo ""
  echo " All of these arguments should be supplied directly through run-experiment.sh and"
  echo " if all is well, require no intervention."
  echo ""
  exit 1
}

prefix=""
showHeader=false
fa=""
fb=""
fo=""
fm=""
logfile=""

while [[ "$#" -gt 0 ]]; do
  arg=$1;
  case $arg in
    --header) showHeader=true; break ;;
    --prefix) prefix=$2; shift ;;
    --fa) fa=$2; shift ;;
    --fb) fb=$2; shift ;;
    --fo) fo=$2; shift ;;
    --fm) fm=$2; shift ;;
    --log) logfile=$2; shift ;;
    --rest) shift; break;;
    *) showHelpPA ;;
  esac
  shift
done

output() {
  if [[ -z "$logfile" ]]; then
    echo "$1" 
  else
    echo "$1" >> "$logfile"
  fi
}

