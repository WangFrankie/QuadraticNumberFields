#!/usr/bin/env bash

set -euo pipefail

lake env lean --run QNFBlueprintMain.lean --output _out/site
cd _out/site/html-multi
python3 -m http.server "${PORT:-8000}"
