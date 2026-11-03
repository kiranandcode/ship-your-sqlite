#!/bin/bash
# Clone Certora/clean at the pinned commit into build/clean/src (gitignored).
set -euo pipefail
. "$(dirname "$0")/env.sh"
mkdir -p "$CLEAN_DIR"
if [ ! -d "$CLEAN_SRC/.git" ]; then
  git clone -q "$CLEAN_REPO" "$CLEAN_SRC"
fi
git -C "$CLEAN_SRC" fetch -q origin "$CLEAN_COMMIT" 2>/dev/null || true
git -C "$CLEAN_SRC" checkout -q "$CLEAN_COMMIT"
echo "clean at $(git -C "$CLEAN_SRC" rev-parse HEAD) in $CLEAN_SRC"
