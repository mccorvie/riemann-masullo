import Lean
open Lean

/-!
Prints one line per declaration of the given modules: its kind, its name, a hash of its type
and, for definitions, a hash of its body, followed by `SORRY` if that body contains `sorry` or
if the declaration's statement does. Comparing the output for two versions of the project
shows whether a change altered the statement of anything that already existed.

    lake env lean --run scripts/Signatures.lean RiemannMasullo.AppA_AlgebraicNT.Sec1 ...

Private declarations are left out, since a prover may rework its own helpers. With `--all` as
the first argument, private definitions, instances and local notations are listed as well, under
their full names (`_private.<module>.0.<name>`); the pull request check uses this to notice a
change that adds something other than theorems.

Use `scripts/signatures.sh`, which builds first and passes every module of the library.
-/

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

/-- Whether some component of the name is one Lean generates (`match_1`, `_proof_2`, a number). -/
def hasAuxComponent : Name → Bool
  | .anonymous => false
  | n@(.str p _) => n.isInternalDetail || hasAuxComponent p
  | .num _ _ => true

def main (args : List String) : IO UInt32 := do
  let (all, args) := match args with
    | "--all" :: rest => (true, rest)
    | _ => (false, args)
  initSearchPath (← findSysroot)
  let modules := args.toArray.map (·.toName)
  let env ← importModules (modules.map ({ module := · })) {} (trustLevel := 1024)
  let wanted : Std.HashSet Name := Std.HashSet.ofArray modules
  let mut lines : Array String := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless wanted.contains env.header.moduleNames[idx.toNat]! do continue
    if isPrivateName name then
      unless all do continue
      if let .thmInfo _ := info then continue
      if hasAuxComponent ((privateToUserName? name).getD name) then continue
    else if name.isInternalDetail then continue
    -- A definition is marked when `sorry` occurs in its own body, including in a proof field.
    -- Any declaration is marked when `sorry` occurs in its statement: a hypothesis kept in a
    -- `variable` can fail to elaborate where it is used and become `sorry` with no error.
    let inType := info.type.getUsedConstants.contains ``sorryAx
    let body := match info with
      | .defnInfo d =>
        s!" {d.value.hash}" ++
          (if inType || d.value.getUsedConstants.contains ``sorryAx then " SORRY" else "")
      | _ => if inType then " SORRY" else ""
    lines := lines.push s!"{kindOf info} {name} {info.type.hash}{body}"
  for line in lines.qsort (· < ·) do
    IO.println line
  return 0
