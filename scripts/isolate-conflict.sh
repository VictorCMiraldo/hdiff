#!/bin/bash
set -uo pipefail

vaultdir="."
dataset="dataset"
digemopts=""
id1=""
id2=""

function showUsage() {
  echo "usage: ./isolate-conflict.sh [options] <id1> <id2>"
  echo "  Copies the files in /dataset/*/*-commit1-commit2/ such that"
  echo "  commit1 and commit2 are identified by id1 and id2 into a"
  echo "  specified location, by default it is: $vaultdir/vault"
  echo ""
  echo "  Options are:"
  echo ""
  echo "    -d , --dataset path/to/dataset/"
  echo "      Specifies where should we look for the conflicts"
  echo "      Defaults to '$dataset'"
  echo ""
  echo "    -v , --vault-dir path/to/isolation/"
  echo "      Specivies the destination the conflict should be put."
  echo "      Note that a folder called 'vault' will be created in the destination."
  echo "      Defaults to '$vaultdir'"
  echo ""
  echo "    -r , --run \"opts-to-digem\""
  echo "      Instead of copying the conflicting files, run 'digem'"
  echo "      inside the found folder"
  echo ""
  echo "   -m , --run-merge"
  echo "     The same as '-r \"merge A.lua O.lua B.lua\", just easier to type."
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
         -v|--vault-dir) vaultdir="${1?'missing argument to --vault-dir'}" ; shift ;;
         -r|--run) digemopts="${1?'missing argument to --run'}"; shift ;;
         -m|--run-merge) digemopts="merge A.lua O.lua B.lua" ;;
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

if [[ -z "$dataset" ]]; then
  echo "Dataset is empty; I won't search the whole file system"
  exit 1
fi

tgt=$(find "$dataset/" -name "*-$id1*-$id2*" -type d)
tgtn=$(echo "$tgt" | wc -l)
if [[ "$tgtn" -ne "1" ]]; then
  echo "Too many targets, please get more specific id's"
  exit 1;
else
  # We just want to isolate the conflicts to a specific location
  if [[ -z "$digemopts" ]]; then
    echo "Copying files:"
    echo "  from $tgt" 
    echo "  to   $vaultdir/vault"

    rm -f $vaultdir/vault/*
    mkdir -p "$vaultdir/vault"
    cp $tgt/* $vaultdir/vault

    

    echo "Making link to original dir"
    linkname="${tgt##*/}"
    ln -sr $tgt $vaultdir/vault/$linkname
  # Or we just want to run 'digems' there
  else
    (cd $tgt/ && digem $digemopts ; echo "[exited with $?]")
  fi
fi

