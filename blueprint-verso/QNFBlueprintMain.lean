import VersoManual
import VersoBlueprint.PreviewManifest
import QNFBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.manualMainWithPreviewData
    (%doc QNFBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
