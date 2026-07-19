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

The former leanblueprint/LeanArchitect sources are retained verbatim under
`blueprint/legacy/`. The migrated chapter also keeps adjacent TeX witnesses for
all labeled statements and proofs, while `leanarchitect-nodes.json` preserves
the generated LeanArchitect node data used during the migration.
