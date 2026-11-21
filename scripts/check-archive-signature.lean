import Lean

/-!
Check that `KTheoryBound.archive_bound` (stated with `sorry`) has exactly the same statement
as the archive's proved theorem `UpperTheory.V.SmallClassNumbers.bound`.

The archive theorem is read from the single file `CorGKOf.olean` with `readModuleData`,
without loading that module's 170k-module import closure. Our declaration is loaded from the
light module `KTheoryBound.ArchiveInput`.

Run with:  lake env lean --run scripts/check-archive-signature.lean
-/

open Lean

def archiveModule : Name :=
  `Development.AutomorphicArithmetic.AutomorphicVarieties.SmallClassNumbers.CorGKOf

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  -- the archive's theorem, from its own compiled file
  let path ← findOLean archiveModule
  let (data, _) ← readModuleData path
  let some (.thmInfo arch) := data.constants.find? (·.name == `UpperTheory.V.SmallClassNumbers.bound)
    | IO.eprintln s!"archive theorem not found in {path}"; return 1
  -- our restatement, from the light module
  let env ← importModules #[{ module := `KTheoryBound.ArchiveInput }] {}
  let some ours := env.find? `KTheoryBound.archive_bound
    | IO.eprintln "KTheoryBound.archive_bound not found"; return 1
  IO.println s!"archive file:          {path}"
  IO.println s!"archive  bound : {arch.type}   (universe params {arch.levelParams})"
  IO.println s!"ours archive_bound : {ours.type}   (universe params {ours.levelParams})"
  -- the type both sides refer to must be the archive's own definition, present in our environment
  let expected := Expr.const `UpperTheory.V.SmallClassNumbers.Bound []
  unless (env.find? `UpperTheory.V.SmallClassNumbers.Bound).isSome do
    IO.eprintln "Bound is not in our environment"; return 1
  if arch.type == expected && ours.type == expected &&
      arch.levelParams.isEmpty && ours.levelParams.isEmpty then
    IO.println "OK: identical statements (both are the constant UpperTheory.V.SmallClassNumbers.Bound)"
    return 0
  else
    IO.eprintln "MISMATCH between the archive theorem and our restatement"
    return 1
