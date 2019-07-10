## This is not a standalone script; but meant to be passed to
## scripts/run-experiments.sh
set -uo pipefail

timeout="5s"
whereami=$(basename $(pwd))

fa=$(find . -name "A.*")
fo=$(find . -name "O.*")
fb=$(find . -name "B.*")

timeout "${timeout}" digem merge "$fa" "$fo" "$fb"
res=$?
case $res in
  0) echo "success"               ;;
  1) echo "conflicting"           ;;
  2) echo "panic";         exit 1 ;;
  *) echo "unknown($res)"; exit 1 ;;
esac

exit 1
