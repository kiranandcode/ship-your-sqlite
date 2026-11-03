#!/bin/bash
# Download the pinned SQLite amalgamation into build/sqlite and check its SHA3-256
# against the value published on sqlite.org/download.html.
set -euo pipefail
. "$(dirname "$0")/env.sh"
mkdir -p "$SQLITE_DIR"
zip="$SQLITE_DIR/sqlite-amalgamation-$SQLITE_VERNUM.zip"
if [ ! -f "$zip" ]; then
  curl -fsSL -o "$zip.part" "https://sqlite.org/$SQLITE_YEAR/sqlite-amalgamation-$SQLITE_VERNUM.zip"
  mv "$zip.part" "$zip"
fi
got=$(openssl dgst -sha3-256 -r "$zip" | cut -d' ' -f1)
if [ "$got" != "$SQLITE_SHA3_256" ]; then
  echo "SHA3-256 mismatch for $zip: $got" >&2; exit 1
fi
if [ ! -f "$SQLITE_SRC/sqlite3.c" ]; then
  (cd "$SQLITE_DIR" && unzip -q -o "$zip")
fi
echo "sqlite $SQLITE_VERSION in $SQLITE_SRC"; ls -l "$SQLITE_SRC"
