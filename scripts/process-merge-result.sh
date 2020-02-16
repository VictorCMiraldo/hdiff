#! /bin/bash
set -euo pipefail

showUsage() {
  echo "Usage: process-merge-result.sh <log-file>"
  echo ""
  echo "  Log file must have been produced by ./run-experiment.sh ... merge.sh ..."
  echo "  Or be in the format:"
  echo ""  
  echo "  <reponame-commitId-objId> <height> <mode> <opq-mode> <global|local> <result>"
  echo ""
  echo "  where <height>; <mode>; <opq-mode> and <global|local> must be /the same/ througout."
  echo ""

  exit 1
}

if [[ $# -ne 1 ]]; then
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
  END           { print " success+mdif: " (SUCC + MDIF) " mdiff: " MDIF " conf: " CONF " parse-error: " PERR " timeout: " TOUT " other: " OTHER }'

while IFS= read -r header; do 
  cat $1 | grep "$header" | cut -d' ' -f6 | sort | uniq -c | awk "$awkScript" | xargs -I{} echo "$header {}"
done < <(cat $1 | cut -d' ' -f2,3,4,5 | sort | uniq)


