import ArtformScores.GravityBridge.Native.Retrospective.SourceCost

open Lean Elab Command
namespace Artform.Scores.GravityBridge.CostAudit
partial def proofTreeNodes : Expr → Nat
  | .app f a => 1 + proofTreeNodes f + proofTreeNodes a
  | .lam _ t b _ => 1 + proofTreeNodes t + proofTreeNodes b
  | .forallE _ t b _ => 1 + proofTreeNodes t + proofTreeNodes b
  | .letE _ t v b _ => 1 + proofTreeNodes t + proofTreeNodes v + proofTreeNodes b
  | .mdata _ b => 1 + proofTreeNodes b
  | .proj _ _ b => 1 + proofTreeNodes b
  | _ => 1
partial def proofDagNodes (roots : List Expr) : Nat := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut todo := roots
  while !todo.isEmpty do
    let e := todo.head!
    todo := todo.tail!
    if seen.contains e then continue
    seen := seen.insert e
    match e with
    | .app f a => todo := f :: a :: todo
    | .lam _ t b _ | .forallE _ t b _ => todo := t :: b :: todo
    | .letE _ t v b _ => todo := t :: v :: b :: todo
    | .mdata _ b | .proj _ _ b => todo := b :: todo
    | _ => pure ()
  return seen.size
run_cmd do
  let env ← getEnv
  for n in [`Artform.Scores.GravityBridge.Native.schurCovector_eq,
      `Artform.Scores.GravityBridge.Native.Retrospective.factorized_schur_same] do
    let some ci := env.find? n | throwError "Missing target"
    let some v := ci.value? (allowOpaque := true) | throwError "Missing proof"
    let mut seen : NameSet := {}
    let mut todo := [n]
    let mut closureNodes := 0
    let mut closureCount := 0
    let mut closureExprs : List Expr := []
    while !todo.isEmpty do
      let q := todo.head!
      todo := todo.tail!
      if seen.contains q then continue
      seen := seen.insert q
      if !(`Artform).isPrefixOf q then continue
      let some info := env.find? q | continue
      closureCount := closureCount + 1
      let mut ds := info.type.getUsedConstants
      if let some b := info.value? (allowOpaque := true) then
        closureExprs := b :: closureExprs
        closureNodes := closureNodes + proofTreeNodes b
        ds := ds ++ b.getUsedConstants
      todo := todo ++ ds.toList
    let data := Json.mkObj [("target", toJson n.toString),
      ("local_tree_nodes", toJson (proofTreeNodes v)),
      ("local_structural_DAG_nodes", toJson (proofDagNodes [v])),
      ("artform_closure_structural_DAG_nodes", toJson (proofDagNodes closureExprs)),
      ("raw_Expr_render_characters", toJson (toString v).length),
      ("artform_closure_tree_nodes", toJson closureNodes),
      ("artform_closure_declarations", toJson closureCount)]
    logInfo m!"{data.compress}"

end Artform.Scores.GravityBridge.CostAudit
