#!/bin/bash
set -uo pipefail

vault="vault"
dataset="dataset"
id1=""
id2=""

function showUsage() {
  echo "usage: ./isolate-conflict.sh [options] <id1> <id2>"
  echo "  Copies the files in /dataset/*/*-commit1-commit2/ such that"
  echo "  commit1 and commit2 are identified by id1 and id2 into a"
  echo "  specified location, by default it is: $vault"
  echo ""
  echo "  Options are:"
  echo ""
  echo "    -d , --dataset path/to/dataset/"
  echo "      Specifies where should we look for the conflicts"
  echo "      Defaults to '$dataset'"
  echo ""
  echo "    -v , --vault path/to/isolation/vault"
  echo "      Specivies the destination the conflict should be put."
  echo "      Defaults to '$vault'"
  echo ""
  exit 0
}

case "$#" in
  0) showUsage           ;;
  1) showUsage           ;;
  2) id1="$1"; id2="$2"; ;;
  *) while [[ "$1" =~ ^-.* ]]; do
       arg=$1;
       shift;
       case $arg in
         -d|--dataset) dataset="${1?'missing argument to --skip'}" ; shift ;;
         -v|--vault) vault="${1?'missing argument to --vault'}" ; shift ;;
         *) showUsage ;;
       esac
     done
     if [[ "$#" -eq "2" ]]; then
       id1="$1" 
       id2="$2"
    else
      showUsage
    fi ;;
esac

tgt=$(find "$dataset/" -name "*-$id1*-$id2*" -type d)
tgtn=$(echo "$tgt" | wc -l)
if [[ "$tgtn" -ne "1" ]]; then
  echo "Too many targets, please get more specific id's"
  exit 1;
else
  echo "Copying files:"
  echo "  from $tgt" 
  echo "  to   $vault"

  mkdir -p "$vault"
  cp $tgt/* $vault/

  echo "Making link to original dir"
  linkname="${tgt##*/}"
  ln -sr $tgt $vault/$linkname
fi

