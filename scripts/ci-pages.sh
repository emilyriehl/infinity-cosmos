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
python3 - <<'PY'
from pathlib import Path
import re

chapter = Path("InfinityCosmosBlueprint/Chapters/InfinityCosmoi.lean").read_text()
blocks = re.findall(r"^```tikzcd\n(.*?)\n```$", chapter, flags=re.MULTILINE | re.DOTALL)
expected = len(blocks)
html = "\n".join(
    path.read_text() for path in Path("_out/site/html-multi").rglob("*.html")
)
rendered = html.count('class="tikzcd-diagram"')
if rendered != expected:
    raise SystemExit(f"expected {expected} rendered TikZ-CD diagrams, found {rendered}")
if "viewBox='0 0 0 0'" in html:
    raise SystemExit("an empty TikZ-CD SVG was generated")
expected_environments = sum(max(1, block.count(r"\begin{tikzcd}")) for block in blocks)
generated_tex = Path("_out/site/tex/main.tex").read_text()
rendered_environments = generated_tex.count(r"\begin{tikzcd}")
if rendered_environments != expected_environments:
    raise SystemExit(
        f"expected {expected_environments} TikZ-CD environments in TeX, "
        f"found {rendered_environments}"
    )
print(
    f"TikZ-CD rendering OK: {rendered} HTML diagrams and "
    f"{rendered_environments} TeX environments."
)
PY
