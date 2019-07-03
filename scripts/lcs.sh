#! /bin/bash

if [[ $# -ne "2" ]]; then
  echo "I need two files"
  exit 1
fi

lenB=$(wc -l "$2" | cut -d' ' -f 1)
dels=$(diff "$1" "$2" | grep "^>" | wc -l | cut -d' ' -f 1)

echo $((lenB - dels))
