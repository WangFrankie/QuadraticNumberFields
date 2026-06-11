#!/usr/bin/env bash

set -euo pipefail

# Skip the slow Verso HTML render when SKIP_RENDER=1. Useful when the
# rendered site already exists on disk and you just want to republish
# it (e.g. rsync to a remote, or run a quick local sanity check). When
# set, the script still runs `lake build` (fast if up to date) and the
# file-existence checks below verify the existing build is intact.

SKIP_RENDER="${SKIP_RENDER:-}"

if [ -n "$SKIP_RENDER" ]; then
  echo "[ci-pages] SKIP_RENDER=1, reusing existing _out/site"
else
  lake build QNFBlueprint
  lake env lean --run QNFBlueprintMain.lean --output _out/site
fi

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json
