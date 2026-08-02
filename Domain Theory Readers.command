#!/bin/zsh
set -e

cd "$(dirname "$0")"
python3 docs/start_reader.py "$@"
