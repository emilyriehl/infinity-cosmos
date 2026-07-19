import VersoBlueprint
import VersoBlueprint.Macros

open Lean
open Verso Doc Elab
open Verso.Output (Html)
open Verso.Genre Manual

namespace InfinityCosmosBlueprint.Tikz

private def standaloneSource (texPrelude source : String) : String :=
  String.intercalate "\n" [
    "\\documentclass[varwidth,border=2pt]{standalone}",
    "\\usepackage{amsmath,amssymb,mathtools}",
    "\\usepackage{tikz-cd}",
    texPrelude,
    "\\begin{document}",
    source,
    "\\end{document}",
    ""
  ]

private def processFailure (name : String) (out : IO.Process.Output) : String :=
  let details := (out.stdout ++ "\n" ++ out.stderr).trimAscii.toString
  let lines := details.splitOn "\n"
  let details := String.intercalate "\n" (lines.drop (lines.length - 40))
  s!"{name} exited with code {out.exitCode}.{if details.isEmpty then "" else "\n" ++ details}"

private def runProcess (name : String) (args : Array String) (cwd : System.FilePath) : IO (Except String Unit) := do
  try
    let out ← IO.Process.output { cmd := name, args, cwd := some (System.FilePath.toString cwd) }
    if out.exitCode == 0 then
      pure (.ok ())
    else
      pure (.error (processFailure name out))
  catch e =>
    pure (.error s!"could not run {name}: {e}")

private def svgElement (idPrefix svg : String) : Except String String :=
  match svg.splitOn "<svg" with
  | _prefix :: suffix :: _ =>
      let svg := "<svg" ++ suffix
      if svg.contains "viewBox='0 0 0 0'" then
        .error "dvisvgm produced an empty SVG"
      else
        let fullPrefix := "tikzcd-" ++ idPrefix ++ "-"
        let svg := svg.replace "id='" ("id='" ++ fullPrefix)
        let svg := svg.replace "href='#" ("href='#" ++ fullPrefix)
        let svg := svg.replace "url(#" ("url(#" ++ fullPrefix)
        .ok svg
  | _ => .error "dvisvgm output did not contain an SVG element"

private def renderSvg (texPrelude source : String) : IO (Except String String) := do
  let key := toString <| hash ("infinity-cosmos-tikzcd-v2\n" ++ texPrelude ++ "\n" ++ source)
  let cacheDir := (← IO.Process.getCurrentDir) / ".cache" / "verso-tikz" / key
  let texPath := cacheDir / "diagram.tex"
  let dviPath := cacheDir / "diagram.dvi"
  let svgPath := cacheDir / "diagram.svg"
  if ← svgPath.pathExists then
    match svgElement key (← IO.FS.readFile svgPath) with
    | .ok svg => return .ok svg
    | .error _ => IO.FS.removeFile svgPath

  IO.FS.createDirAll cacheDir
  IO.FS.writeFile texPath (standaloneSource texPrelude source)
  match ← runProcess "dvilualatex"
      #["--no-shell-escape", "-interaction=nonstopmode", "-halt-on-error", "-file-line-error",
        texPath.fileName.getD "diagram.tex"]
      cacheDir with
  | .error message => return .error message
  | .ok () => pure ()
  match ← runProcess "dvisvgm"
      #["--no-fonts", "--exact", "--output=diagram.svg", dviPath.fileName.getD "diagram.dvi"]
      cacheDir with
  | .error message => return .error message
  | .ok () => pure <| svgElement key (← IO.FS.readFile svgPath)

block_extension Block.tikzcd (source : String) (svg : String) where
  data := Json.arr #[.str source, .str svg]
  extraCss := [r#"
.tikzcd-diagram {
  background: #fff;
  color: #000;
  display: flex;
  justify-content: center;
  margin: 1rem 0;
  overflow-x: auto;
  padding: 0.75rem;
}
.tikzcd-diagram > svg {
  display: block;
  height: auto;
  max-width: 100%;
}
"#]
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .arr #[.str _source, .str svg] := data
        | reportError "Malformed tikzcd diagram data" *> pure .empty
      pure {{<div class="tikzcd-diagram" role="img" aria-label="Commutative diagram">{{Html.text false svg}}</div>}}
  usePackages := ["\\usepackage{tikz-cd}"]
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _ _ _ data _ => do
      let .arr #[.str source, .str _svg] := data
        | reportError "Malformed tikzcd diagram data" *> pure .empty
      pure (.raw ("\n" ++ source ++ "\n"))

private def completeSource (source : String) : String :=
  let source := source.trimAscii.toString
  if source.contains "\\begin{tikzcd}" then
    source
  else
    "\\begin{center}\n\\begin{tikzcd}\n" ++ source ++ "\n\\end{tikzcd}\n\\end{center}"

/--
Render TikZ-CD source as SVG in HTML while preserving the original TikZ for TeX/PDF output.
The block accepts either a complete TeX fragment containing a `tikzcd` environment or just the
contents of a `tikzcd` environment.
-/
@[code_block]
def _root_.tikzcd : CodeBlockExpanderOf Unit
  | _, sourceSyntax => do
    let source := completeSource sourceSyntax.getString
    let texPrelude ← Informal.Macros.getTexPrelude
    match ← liftM <| renderSvg texPrelude source with
    | .ok svg =>
        ``(Verso.Doc.Block.other (Block.tikzcd $(quote source) $(quote svg)) #[])
    | .error message =>
        throwErrorAt sourceSyntax m!"Failed to render TikZ-CD diagram.\n{message}"

end InfinityCosmosBlueprint.Tikz
