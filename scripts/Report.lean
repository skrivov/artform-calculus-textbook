import Lean
import ArtformTextbook

/-!
# The status report

`lake env lean --run scripts/Report.lean` prints, as JSON, one entry for each
declaration tagged `@[book "label"]` (see `ArtformTextbook/Meta/Book.lean`),
sorted by name:

* `statement`, for a `def … : Prop`. It gives the statement's text, and its
  *surface*: the `Artform` declarations it reaches through definitions, each
  with its text. It also gives the exact terms of both, from which
  `scripts/status.py` takes the two review hashes.
* `proof`, for a `theorem`. It gives the statement constant the theorem
  proves, and the axioms the theorem uses.
* `definition`, for anything else. It gives its text.

`main` is `unsafe` because it runs the library's initializers, which the
pretty-printer needs to print notation.
-/

open Lean Meta

/-- The `Artform` declarations that `start` reaches through definitions, but
not through proofs, sorted by name. -/
partial def surface (env : Environment) (start : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut todo : List Name := [start]
  let mut out : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if !(`Artform).isPrefixOf n then continue
    if n != start then out := out.push n
    let mut used := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then
      if !ci.isTheorem then used := used ++ v.getUsedConstants
    if let .inductInfo ii := ci then
      for c in ii.ctors do
        if let some cc := env.find? c then used := used ++ cc.type.getUsedConstants
    todo := todo ++ used.toList
  return out.qsort (·.toString < ·.toString)

/-- The readable text of a declaration: its type, its value if it is a
definition, its constructors if it is an inductive type. -/
def render (n : Name) : MetaM String := do
  let ci ← getConstInfo n
  let ty ← ppExpr ci.type
  if !ci.isTheorem then
    if let some v := ci.value? (allowOpaque := true) then
      return s!"{n} : {ty} :=\n  {← ppExpr v}"
  if let .inductInfo ii := ci then
    let ctors ← ii.ctors.mapM fun c => do
      return s!"\n  | {c} : {← ppExpr (← getConstInfo c).type}"
    return s!"{n} : {ty}" ++ String.join ctors
  return s!"{n} : {ty}"

/-- The exact term of a declaration, as Lean stores it. -/
def term (n : Name) : MetaM String := do
  let ci ← getConstInfo n
  let mut s := s!"{n} : {ci.type}"
  if !ci.isTheorem then
    if let some v := ci.value? (allowOpaque := true) then
      s := s ++ s!" := {v}"
  if let .inductInfo ii := ci then
    for c in ii.ctors do
      s := s ++ s!"\n  | {c} : {(← getConstInfo c).type}"
  return s

/-- One entry of the report. -/
def entry (n : Name) (ci : ConstantInfo) (label : String) : MetaM Json := do
  let base : List (String × Json) := [("label", toJson label), ("decl", toJson n.toString)]
  if ci.isTheorem then
    let axs : Array Name ← collectAxioms n
    let proves := match ci.type with
      | .const s _ => s.toString
      | _ => ""
    return Json.mkObj <| ("kind", toJson "proof") :: base ++
      [("proves", toJson proves), ("axioms", toJson (axs.map Name.toString))]
  else if ci.type.isProp then
    let surf := surface (← getEnv) n
    return Json.mkObj <| ("kind", toJson "statement") :: base ++
      [("text", toJson (← render n)), ("surface", toJson (← surf.mapM render)),
       ("terms", toJson (← (#[n] ++ surf).mapM term))]
  else
    return Json.mkObj <| ("kind", toJson "definition") :: base ++
      [("text", toJson (← render n))]

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `ArtformTextbook }] {} (trustLevel := 1024)
    (loadExts := true)
  let ctx : Core.Context := { fileName := "<report>", fileMap := default }
  let (rows, _) ← (MetaM.run' do
      let env ← getEnv
      let mut rows : Array (String × Json) := #[]
      for (n, ci) in (env.constants.toList : List (Name × ConstantInfo)) do
        if let some label := Artform.bookAttr.getParam? env n then
          rows := rows.push (n.toString, ← entry n ci label)
      return (rows.qsort (·.1 < ·.1)).map (·.2)).toIO ctx { env }
  IO.println (Json.arr rows).pretty
