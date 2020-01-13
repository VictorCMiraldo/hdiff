#! /bin/bash
set -euo pipefail

function showUsage() {
  echo "./scripts/mine-data folder/with/data-sources path/to/dataset"
  echo ""
  echo "  Where 'folder/with/data-sources' should contain files containing github addresses."
  echo "  Suppose we have: 'tree folder/with/data-sources' returning:"
  echo ""
  echo "   $ tree folder/with/data-sources"
  echo "     dataset"
  echo "     ├── lua"
  echo "     ├── clj"
  echo "     ├── sh"
  echo ""
  echo "  Then we will create 'path/to/dataset/conflicts-lua/...' etc; where"
  echo "  all the conflicts will be placed."
  echo ""
  exit 1
}

if [[ "$#" -ne "2" ]]; then
  showUsage
fi

datasrc=$1
dataset=$2

if [[ -d "$dataset" ]]; then
  echo "Specified dataset already exists"
  showUsage
fi

mkdir -p "$dataset"
for i in $(ls -1 "$datasrc"); do
  echo "Mining repositories in $i"
  target="$dataset/conflicts-$i"
  cat "$datasrc/$i" | ./scripts/mine-repositories.sh "$target" "$i"
done
