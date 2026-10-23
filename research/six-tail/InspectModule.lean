import Lean
open Lean

/- Read-only verification tooling: inspect compiled declaration names to select
headlines for the unchanged checker. This file is not imported by any proof. -/
unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  for arg in args do
    let file ← findOLean arg.toName
    let mut files := #[file]
    let server := OLeanLevel.server.adjustFileName file
    if ← server.pathExists then
      files := files.push server
      let priv := OLeanLevel.private.adjustFileName file
      if ← priv.pathExists then files := files.push priv
    let parts ← readModuleDataParts files
    if h : parts.size = 0 then
      throw <| IO.userError "No compiled module data"
    else
      let data := parts[parts.size - 1].1
      let mut names : Array String := #[]
      for name in data.constNames, ci in data.constants do
        if let .thmInfo val := ci then
          if val.levelParams.isEmpty && !name.isInternal then names := names.push name.toString
      IO.println <| Json.compress <| Json.mkObj [
        ("module", toJson arg), ("constants", toJson data.constants.size),
        ("theorems", toJson names)]
