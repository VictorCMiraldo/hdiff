#! /bin/bash
set -euo pipefail

function showUsage() {
  echo "cat repository-db | ./scripts/mine-repositories path/to/dataset/tgt language"
  echo ""
  echo "  The repository-db is a file with one address per line; we'll clone all"
  echo "  the repositories in there and mine their conflicts with the scripts/mine-conflicts"
  echo "  script"
  echo ""
  exit 1
}

if [[ "$#" -ne "2" ]]; then
  showUsage
fi

target="$1"
lang="$2"

mkdir -p "$target"

dir=$(mktemp -d)
echo "Working in $dir"
function earlyexit() {
  rm -rf $dir/*
  rmdir $dir
}
trap earlyexit SIGINT SIGTERM SIGQUIT

function getData() {
  lynx -dump -nolist index.html | grep "$1" | head -n 1 | sed 's/[^0-9]*//g'
}

while read -r line; do
  pushd $dir
  wget -O index.html $line 
  commits=$(getData "commits")
  contributors=$(getData "contributors")
  stars=$(getData "Star")
  forks=$(getData "Fork")
  repo=${line##*.com/}
  git clone "git@github.com:${line##*.com/}"

  popd
  echo "$repo , ${commits} commits, ${contributors} contrib, ${stars} stars, ${forks} forks" >> $target/metadata
  ./scripts/mine-conflicts.sh $dir/$(basename "$repo") $target $lang
done
  
