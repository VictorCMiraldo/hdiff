#! /bin/bash
set -uo pipefail

GIT_WORK_TREE=""
GIT_DIR=""

function showUsage() {
  echo "./mine-conflicts.sh path/to/repository path/to/dataset/tgt language"
  echo ""
  echo "  Example usage: Mine all the conflicts for .el files in repository local/repos/helm"
  echo "  and place them in ./conflicts-el"
  echo ""
  echo "  ./mine-conflicts local/repos/helm ./conflicts-el el"
  echo ""
}

if [[ "$#" -ne "3" ]]; then
  showUsage
  exit 1
fi

repo="$1"
target="$2"
lang="$3"

function earlyexit {
  if ! [[ -z "$repo" ]]; then
    git -C $repo merge --abort
    git -C $repo reset -q --hard
    git -C $repo clean -fdxq
    git -C $repo checkout master
    exit 1
  fi
}

trap earlyexit SIGINT SIGTERM SIGQUIT

echo "Mining $repo"
old_branch=$(git -C $repo symbolic-ref --short HEAD)

for commit in $(git -C $repo rev-list --merges HEAD); do
  parents=$(git -C $repo log -1 --format=%P $commit)
  fst=${parents%% *}
  rest=${parents#* }
  git -C $repo checkout -f -q $fst
  git -C $repo merge --no-commit $rest >/dev/null 2>&1
  if git -C $repo ls-files --unmerged | grep -q '^'; then
    echo "found conflict in $repo - $commit"
    while read -r line; do
      objO=$(echo $line | cut -d' ' -f 1)
      objA=$(echo $line | cut -d' ' -f 2)
      objB=$(echo $line | cut -d' ' -f 3)
      fullname=$(echo $line | cut -d' ' -f 4)
      extension=$(echo $fullname | cut -d. -f 2)
      if [ "$extension" == "$lang" ]; then
        towrite="$target/$(basename $repo)-$commit-$objO"
        mkdir -p "$towrite"
        git -C $repo cat-file -p $objO > "$towrite/O.$lang"
        git -C $repo cat-file -p $objA > "$towrite/A.$lang"
        git -C $repo cat-file -p $objB > "$towrite/B.$lang"
        git -C $repo show $commit:$fullname > "$towrite/M.$lang"
      fi
    done < <( git -C $repo ls-files --unmerged \
            | awk '{ if ($3 == 1) F1=$2; \
                     if ($3 == 2) F2=$2; \
                     if ($3 == 3) { F3=$2 ; print F1 " " F2 " " F3 " " $4 }}')
    git -C $repo merge --abort
  fi
  git -C $repo reset -q --hard
  git -C $repo clean -fdxq
done
git -C $repo checkout -f -q $old_branch

