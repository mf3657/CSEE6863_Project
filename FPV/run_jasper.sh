#!/bin/bash

DESIGN_SCRIPT="$1"

if [ -z "$DESIGN_SCRIPT" ]; then
  echo "usage: $0 <design>"
  exit 1
fi

jg -fpv $DESIGN_SCRIPT
