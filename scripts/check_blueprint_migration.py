#!/usr/bin/env python3
"""Check that the Verso port covers every active legacy Blueprint node."""

from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CHAPTER = ROOT / "InfinityCosmosBlueprint/Chapters/InfinityCosmoi.lean"
LEGACY_TEX = ROOT / "blueprint/legacy/content.tex"
LEGACY_NODES = ROOT / "blueprint/legacy/leanarchitect-nodes.json"
BIBLIOGRAPHY = ROOT / "InfinityCosmosBlueprint/Bibliography.lean"

NODE_ENVS = (
    "theorem|thm|lemma|lem|proposition|prop|corollary|cor|"
    "definition|defn|con|dig|example|ex|rmk"
)


def active_tex(text: str) -> str:
    lines: list[str] = []
    for line in text.splitlines():
        if line.lstrip().startswith("%"):
            continue
        # This matches TeX's treatment of the unescaped inline comments used by the source.
        lines.append(line.split("%", 1)[0])
    return "\n".join(lines)


def fail(message: str) -> None:
    raise SystemExit(f"Blueprint migration check failed: {message}")


chapter = CHAPTER.read_text()
legacy_tex = LEGACY_TEX.read_text()
node_rows = json.loads(LEGACY_NODES.read_text())

formal_labels = {row["latexLabel"] for row in node_rows}
formal_declarations = {row["name"] for row in node_rows}
informal_labels = set(
    re.findall(
        rf"\\begin\{{(?:{NODE_ENVS})\}}.*?\\label\{{([^}}]+)\}}",
        active_tex(legacy_tex),
    )
)
expected_labels = formal_labels | informal_labels

verso_labels = set(
    re.findall(
        r'^:::(?:theorem|lemma_|proposition|corollary|definition) "([^"]+)"',
        chapter,
        flags=re.MULTILINE,
    )
)
witness_labels = set(
    re.findall(r'^```tex "([^"]+)" \(slot := statement\)', chapter, flags=re.MULTILINE)
)

missing = expected_labels - verso_labels
extra = verso_labels - expected_labels
missing_witnesses = expected_labels - witness_labels
missing_declarations = {name for name in formal_declarations if name not in chapter}
tikz_blocks = re.findall(r"^```tikzcd\n(.*?)\n```$", chapter, flags=re.MULTILINE | re.DOTALL)
visible_tex_blocks = re.findall(
    r"^```tex \(display := source\)\n(.*?)\n```$", chapter, flags=re.MULTILINE | re.DOTALL
)
proof_directives = re.findall(r'^:::proof "([^"]+)"', chapter, flags=re.MULTILINE)
proof_witnesses = re.findall(
    r'^```tex "([^"]+)" \(slot := proof\)', chapter, flags=re.MULTILINE
)
formal_proof_labels = {
    row["latexLabel"] for row in node_rows if (row.get("proof") or {}).get("text")
}
expected_proof_count = len(formal_proof_labels) + len(
    re.findall(r"\\begin\{proof\}", active_tex(legacy_tex))
)

if missing:
    fail(f"missing active labels: {sorted(missing)}")
if extra:
    fail(f"unexpected labels: {sorted(extra)}")
if missing_witnesses:
    fail(f"missing statement TeX witnesses: {sorted(missing_witnesses)}")
if missing_declarations:
    fail(f"missing Lean declaration links: {sorted(missing_declarations)}")
if any(r"\begin{tikzcd}" in block for block in visible_tex_blocks):
    fail("a visible TikZ-CD diagram is still rendered as TeX source")
if not tikz_blocks:
    fail("no native tikzcd blocks found")
if proof_directives != proof_witnesses:
    fail("proof directives and their TeX witnesses differ or are out of order")
if len(proof_directives) != expected_proof_count:
    fail(f"expected {expected_proof_count} proof blocks, found {len(proof_directives)}")

citation_keys = set(re.findall(r"\\cite(?:\[[^]]*\])?\{([^}]+)\}", legacy_tex))
for row in node_rows:
    citation_keys.update(
        re.findall(
            r"\\cite(?:\[[^]]*\])?\{([^}]+)\}",
            json.dumps(row, ensure_ascii=False),
        )
    )
registered_citations = set(re.findall(r'@\[bib "([^"]+)"\]', BIBLIOGRAPHY.read_text()))
if citation_keys - registered_citations:
    fail(f"unregistered citations: {sorted(citation_keys - registered_citations)}")

active_sources = [ROOT / "lakefile.toml", *sorted((ROOT / "InfinityCosmos").rglob("*.lean"))]
architect_references = [
    str(path.relative_to(ROOT))
    for path in active_sources
    if re.search(r"\b(?:LeanArchitect|Architect)\b", path.read_text())
]
if architect_references:
    fail(f"active LeanArchitect references in: {architect_references}")

print(
    "Blueprint migration coverage OK: "
    f"{len(formal_labels)} formal labels + {len(informal_labels)} active TeX-only labels "
    f"= {len(expected_labels)} Verso statements; {len(proof_directives)} proofs, "
    f"{len(citation_keys)} citations, and {len(tikz_blocks)} rendered TikZ-CD blocks registered."
)
