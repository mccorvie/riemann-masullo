import Lean
open Lean

/-!
Lists the declarations of the given modules whose statement (their type) is large as a tree, with
the subterm that accounts for most of that size. One tab-separated line per declaration, largest
tree first:

    name  module  tree-size  in-memory  dominant-subterm

A statement is small in memory, because Lean shares repeated subterms, but `kabstract` (inside
`rw`, `obtain` and `cases` on a term, `generalize`) and parts of `isDefEq` walk the goals built from
it as trees. A term that a notation spells out inside an `abbrev` type is copied into every
instance argument over that type, and the instances nest, so the copies multiply: statements of
10¹³ nodes as a tree, with 20,000 distinct ones, made single proofs take minutes (#5398, #6948).

`dominant-subterm` is the subterm with the largest multiplicity × size among those of 200 to
100,000 nodes, as `head/number-of-arguments multiplicity×size`. That is the term to give a name
(an `abbrev` or `def` of the term itself, which notations then point at). It is `-` for statements
under 10⁸ nodes.

    lake env lean --run scripts/StatementSizes.lean --min 1000000 RiemannMasullo.Ch10_TraceSpectral.Sec1 ...

With `--min N` as the first argument only statements of at least `N` nodes are listed.
-/

/-- Children of a node, in the order a tree walk visits them. -/
def children : Expr → List Expr
  | .app f a => [f, a]
  | .lam _ d b _ | .forallE _ d b _ => [d, b]
  | .letE _ t v b _ => [t, v, b]
  | .proj _ _ x | .mdata _ x => [x]
  | _ => []

/-- The distinct subterms of `e` in post-order, with the size of each as a tree. -/
partial def postOrder (e : Expr) : StateM (Std.HashMap Expr Nat × Array Expr) Nat := do
  if let some n := (← get).1[e]? then return n
  let mut n := 1
  for c in children e do n := n + (← postOrder c)
  modify fun (m, a) => (m.insert e n, a.push e)
  return n

/-- The subterm of `t` with the largest multiplicity × tree size, among those of 200 to 100,000
nodes, as `head/arguments multiplicity×size`. -/
def dominant (t : Expr) (sizes : Std.HashMap Expr Nat) (post : Array Expr) : String := Id.run do
  -- multiplicities: parents before children, which is reverse post-order
  let mut mult : Std.HashMap Expr Nat := ({} : Std.HashMap Expr Nat).insert t 1
  for e in post.reverse do
    let m := mult.getD e 0
    for c in children e do mult := mult.insert c (mult.getD c 0 + m)
  let mut best : Option (Nat × Nat × Nat × Expr) := none
  for e in post do
    let s := sizes.getD e 0
    if 200 ≤ s && s ≤ 100000 then
      let m := mult.getD e 0
      if best.all (·.1 < m * s) then best := some (m * s, m, s, e)
  match best with
  | none => "-"
  | some (_, m, s, e) =>
    let head := match e.getAppFn with
      | .const n _ => toString n
      | .lam .. => "fun"
      | .forallE .. => "∀"
      | .letE .. => "let"
      | .bvar .. => "bound variable"
      | .proj s i _ => s!"{s}.{i + 1}"
      | _ => "_"
    s!"{head}/{e.getAppNumArgs} {m}×{s}"

def main (args : List String) : IO UInt32 := do
  let (minSize, args) := match args with
    | "--min" :: n :: rest => (n.toNat!, rest)
    | _ => (0, args)
  initSearchPath (← findSysroot)
  let modules := args.toArray.map (·.toName)
  let env ← importModules (modules.map ({ module := · })) {} (trustLevel := 1024)
  let wanted : Std.HashSet Name := Std.HashSet.ofArray modules
  let mut rows : Array (Nat × String) := #[]
  for (n, c) in env.constants.toList do
    if n.isInternalDetail then continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless wanted.contains mod do continue
    let t := c.type
    let (tree, (sizes, post)) := (postOrder t).run ({}, #[]) |>.run
    if tree < minSize then continue
    let dom := if tree < 100000000 then "-" else dominant t sizes post
    rows := rows.push (tree, s!"{n}\t{mod}\t{tree}\t{sizes.size}\t{dom}")
  for (_, line) in rows.qsort (fun a b => a.1 > b.1 || (a.1 == b.1 && a.2 < b.2)) do
    IO.println line
  return 0
