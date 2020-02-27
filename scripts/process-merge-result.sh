#! /bin/bash
set -euo pipefail

showUsage() {
  echo "Usage: process-merge-result.sh <log-file1> ... <log-fileN>"
  echo ""
  echo "  Log file must have been produced by ./run-experiment.sh ... merge.sh ..."
  echo "  Or be in the format:"
  echo ""  
  echo "  <reponame-commitId-objId> <height> <mode> <global|local> <result>"
  echo ""
  exit 1
}

if [[ $# -lt 1 ]]; then
  echo "Wron number of arguments"
  showUsage
fi

awkScript='\
  BEGIN         { PERR=0; SUCC=0; CONF=0; TOUT=0; MDIF=0; OTHER=0; }\
  /conflicting/ { CONF=$1  }\
  /merge-diff/  { MDIF=$1  }\
  /success/     { SUCC=$1  }\
  /parse-error/ { PERR=$1  }\
  /timeout/     { TOUT=$1  }\
  /unknown/     { OTHER=$1 }\
  /apply-fail/  { OTHER=$1 }\
  END           { print " success+mdiff: " (SUCC + MDIF) " mdiff: " MDIF " conf: " CONF " parse-error: " PERR " timeout: " TOUT " other: " OTHER }'

while IFS= read -r header; do 
  cat "$@" | grep "$header" | cut -d' ' -f5 | sort | uniq -c | awk "$awkScript" | xargs -I{} echo "$header {}"
done < <(cat "$@" | cut -d' ' -f2,3,4 | sort | uniq)


