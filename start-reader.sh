#!/usr/bin/env sh
set -eu

cd "$(dirname "$0")"
exec "${PYTHON:-python3}" docs/start_reader.py "$@"
