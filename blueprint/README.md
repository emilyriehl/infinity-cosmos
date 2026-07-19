# Blueprint

The active blueprint is written with [Verso Blueprint](https://github.com/leanprover/verso-blueprint):

- `InfinityCosmosBlueprint/Chapters/InfinityCosmoi.lean` contains the document.
- `InfinityCosmosBlueprint/Blueprint.lean` assembles the document, dependency graph, and progress summary.
- `InfinityCosmosBlueprintMain.lean` is the site generator.

Build the HTML site with:

```sh
lake exe vbp build
```

Build HTML and PDF with:

```sh
lake exe vbp build --pdf
```

The generated site is in `_out/site/html-multi` and the PDF is
`_out/site/pdf/main.pdf`.

## TikZ-CD diagrams

Use a `tikzcd` code block for new diagrams:

````lean
```tikzcd
A \arrow[r, "f"] \arrow[d, "g"'] & B \arrow[d, "h"] \\
C \arrow[r, "k"'] & D
```
````

A complete TeX fragment containing a `tikzcd` environment is also accepted when
surrounding markup or environment options are needed. The normal Blueprint build
uses `dvilualatex` and `dvisvgm` to render and cache an SVG for HTML, while PDF
output receives the original TikZ source. Generated SVGs are cached under
`.cache/verso-tikz`; contributors do not need to regenerate or commit image
files manually.

The renderer requires a TeX installation containing `standalone`, `tikz-cd`,
and LuaTeX, together with `dvisvgm`.

The former leanblueprint/LeanArchitect sources are retained verbatim under
`blueprint/legacy/`. The migrated chapter also keeps adjacent TeX witnesses for
all labeled statements and proofs, while `leanarchitect-nodes.json` preserves
the generated LeanArchitect node data used during the migration.
