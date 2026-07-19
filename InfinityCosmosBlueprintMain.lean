import VersoManual
import VersoBlueprint.PreviewManifest
import InfinityCosmosBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

set_option linter.unusedVariables false in
def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc InfinityCosmosBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
