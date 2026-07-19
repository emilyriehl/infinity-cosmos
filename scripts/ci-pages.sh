#!/usr/bin/env bash

set -euo pipefail

rm -rf _out/site
lake exe vbp build --pdf

site=_out/site/html-multi
test -f "$site/index.html"
test -f "$site/-verso-data/blueprint-manifest.json"
test -f "$site/-verso-data/blueprint-html-cache.json"
test -f _out/site/tex/main.tex
test -f _out/site/pdf/main.pdf
python3 scripts/check_blueprint_migration.py
