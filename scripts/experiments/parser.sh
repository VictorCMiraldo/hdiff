## This is not a standalone script; but meant to be passed to
## scripts/run-experiments.sh

set -uo pipefail

whereami=$(basename $(pwd))

fa=$(find . -name "A.*")
fo=$(find . -name "O.*")
fb=$(find . -name "B.*")

files=("$fa" "$fo" "$fb")
for f in ${files[*]}; do
  digem ast --quiet "$f"
  if [[ "$?" -ne "0" ]]; then
    echo "Parse fail: $whereami"
    read -p "(l)ess or continue?" opt
    case $opt in
      l) less $fa ;;
    esac
  fi
done
