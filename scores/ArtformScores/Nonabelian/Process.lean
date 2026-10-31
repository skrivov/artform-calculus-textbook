import ArtformScores.Nonabelian.Kernels
import ArtformTextbook.Ch07.Defs.Composition
/-! # Owned finite coherent branches, gauge relabeling and history sums -/
set_option autoImplicit false
noncomputable section
namespace Artform.Scores.Nonabelian
open Artform Finset

def edge (e : Bool) : Fin 2 := if e then 1 else 0

def replacement (e : Bool) (c : G) : ProcessProfile frame where
  guard _ := True
  reads := {edge e}
  writes := {edge e}
  update x := Function.update x (edge e) c
  guard_reads _ _ _ := Iff.rfl
  update_reads _ _ _ p hp := by
    have he : p=edge e := hp
    subst p
    simp

def curvatureProfile : ProcessProfile frame where
  guard _ := True
  reads := Set.univ
  writes := ∅
  update := id
  guard_reads _ _ _ := Iff.rfl
  update_reads _ _ _ _ hp := False.elim hp
lemma replacement_apply (e : Bool) (c : G) (x : frame.Table) :
    (replacement e c).apply x=Function.update x (edge e) c := by
  classical
  funext p
  by_cases hp : p=edge e
  · subst p; simp [ProcessProfile.apply,replacement]
  · simp [ProcessProfile.apply,replacement,hp]
lemma curvature_apply (x : frame.Table) : curvatureProfile.apply x=x := by
  funext p
  unfold ProcessProfile.apply
  simp only [show curvatureProfile.writes=(∅ : Set (Fin 2)) from rfl,
    Set.mem_empty_iff_false,ite_false]

abbrev Branch : Gate → Type
  | .electric _ => Option G
  | .curvature _ => Option Unit
instance branchFintype (g : Gate) : Fintype (Branch g) := by
  cases g <;> dsimp [Branch] <;> infer_instance
instance branchDecEq (g : Gate) : DecidableEq (Branch g) := by
  cases g <;> dsimp [Branch] <;> infer_instance

def emptyBatch (x : frame.Table) : Batch frame x := ⟨[],by simp⟩
def singleBatch (u : ProcessProfile frame) (x : frame.Table) (hu : u.guard x) : Batch frame x :=
  ⟨[⟨u,hu⟩],by simp⟩
def batch : (g : Gate) → (x : frame.Table) → Branch g → Batch frame x
  | .electric _,x,none => emptyBatch x
  | .electric e,x,some c => singleBatch (replacement e c) x trivial
  | .curvature _,x,none => emptyBatch x
  | .curvature _,x,some _ => singleBatch curvatureProfile x trivial

def coefficient : (g : Gate) → Raw → Branch g → ℚ
  | .electric _,_,none => 0
  | .electric e,x,some c => 1/3-if c=table x (edge e) then 1 else 0
  | .curvature _,_,none => 0
  | .curvature active,x,some _ => phaseSign active x

def commit (g : Gate) (x : Raw) (r : Branch g) : Raw := pair (batch g (table x) r).apply

def Admitted (g : Gate) (x : frame.Table) (b : Batch frame x) : Prop := ∃ r, batch g x r=b
lemma admitted_exhaustive (g : Gate) (x : frame.Table) (b : Batch frame x) :
    Admitted g x b ↔ ∃ r : Branch g, batch g x r=b := Iff.rfl
lemma batch_size (g : Gate) (x : frame.Table) (r : Branch g) :
    (batch g x r).apps.length ≤ 1 := by cases g <;> cases r <;> simp [batch,emptyBatch,singleBatch]

/-- The coefficient at one raw endpoint, summed over all admitted branch events. -/
def branchKernel (g : Gate) (y x : Raw) : ℚ :=
  ∑ r : Branch g, if commit g x r=y then coefficient g x r else 0

lemma commit_electric (e : Bool) (x : Raw) (c : G) :
    commit (.electric e) x (some c)=if e then (x.1,c) else (c,x.2) := by
  change pair ((replacement e c).apply (table x))=_
  rw [replacement_apply]
  cases e <;> simp [edge,pair,table]
lemma commit_curvature (active : Bool) (x : Raw) :
    commit (.curvature active) x (some ())=x := by
  change pair (curvatureProfile.apply (table x))=x
  rw [curvature_apply,pair_table]

lemma electric_branch_formula (e : Bool) (x y : Raw) :
    branchKernel (.electric e) y x=electric e y x := by
  rw [electric_formula]
  cases e <;>
    simp [branchKernel,coefficient,commit_electric,Fintype.sum_option,table,edge,
      Prod.ext_iff,eq_comm]
  · by_cases h : x.2=y.2 <;> simp [h,eq_comm]
  · by_cases h : x.1=y.1 <;> simp [h,eq_comm]

lemma curvature_branch_formula (active : Bool) (x y : Raw) :
    branchKernel (.curvature active) y x=magnetic active y x := by
  simp [branchKernel,coefficient,commit_curvature,Fintype.sum_option,magnetic,
    Matrix.diagonal_apply,eq_comm]
  split_ifs with h
  · subst y; rfl
  · rfl
lemma branch_kernel (g : Gate) (x y : Raw) : branchKernel g y x=gateMatrix g y x := by
  cases g with
  | electric e => exact electric_branch_formula e x y
  | curvature active => exact curvature_branch_formula active x y

def transport : (g : Gate) → G → Branch g ≃ Branch g
  | .electric _,h => Equiv.optionCongr (MulAut.conj h).toEquiv
  | .curvature _,_ => Equiv.refl _
lemma transport_commit (g : Gate) (h : G) (x : Raw) (r : Branch g) :
    commit g (gauge h x) (transport g h r)=gauge h (commit g x r) := by
  cases g with
  | curvature active =>
    cases r with
    | none => rfl
    | some u => cases u; simp only [transport,Equiv.refl_apply,commit_curvature]
  | electric e =>
    cases r with
    | none => rfl
    | some c =>
      change commit (.electric e) (gauge h x) (some (conjugate h c))=_
      rw [commit_electric,commit_electric]
      cases e <;> rfl
lemma transport_coefficient (g : Gate) (h : G) (x : Raw) (r : Branch g) :
    coefficient g (gauge h x) (transport g h r)=coefficient g x r := by
  cases g with
  | curvature active =>
    cases r with
    | none => rfl
    | some u => exact phaseSign_gauge active h x
  | electric e =>
    cases r with
    | none => rfl
    | some c => cases e <;> simp [coefficient,transport,table,edge,gauge,conjugate]

/-- Amplitudes sum all legal event histories; branch labels are not output records. -/
def historyAmplitude : List Gate → Raw → Raw → ℚ
  | [],x,y => if x=y then 1 else 0
  | g::w,x,y => ∑ r : Branch g, coefficient g x r*historyAmplitude w (commit g x r) y
lemma history_compiles (w : List Gate) (x y : Raw) : historyAmplitude w x y=compile w y x := by
  induction w generalizing x y with
  | nil => simp [historyAmplitude,compile,Matrix.one_apply,eq_comm]
  | cons g w ih =>
    simp only [historyAmplitude,compile,Matrix.mul_apply,← branch_kernel,branchKernel]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    simp only [mul_ite,mul_zero,Finset.sum_ite_eq,mem_univ,ite_true]
    rw [ih,mul_comm]

def profiles : Gate → List (ProcessProfile frame)
  | .electric e => Finset.univ.toList.map (replacement e)
  | .curvature _ => [curvatureProfile]
def scheduled (active : Bool) : Fin 3 → Gate := ![.curvature active,.electric false,.electric true]
def nativeLaw (active : Bool) : LawInSteps frame where
  Step := Fin 3
  moves i := profiles (scheduled active i)
  invariants := []
  score :=
    { opens t := ⟨t%3,Nat.mod_lt _ (by decide)⟩
      allowsEmpty _ := True
      period := 3
      period_pos := by decide
      repeats t := by
        constructor
        · apply Fin.ext
          simp
        · rfl }
  moves_legal _ _ _ _ _ _ _ hJ _ := False.elim (List.not_mem_nil hJ)
lemma batch_legal (g : Gate) (x : frame.Table) (r : Branch g) :
    ∀ a ∈ (batch g x r).apps, a.profile ∈ profiles g := by
  cases g with
  | curvature active => cases r <;> simp [batch,emptyBatch,singleBatch,profiles]
  | electric e =>
    cases r with
    | none => simp [batch,emptyBatch]
    | some c => simp [batch,singleBatch,profiles]

/-- A finite coherent realizer chooses weighted legal batches, then sums their amplitudes. -/
structure FiniteCoherentRealizer (L : LawInSteps frame) where
  alternatives : ℕ → Type
  [finiteAlternatives : ∀ t, Fintype (alternatives t)]
  select : ∀ t (x : frame.Table), alternatives t → Batch frame x
  weight : ∀ t, frame.Table → alternatives t → ℚ
  allows : ∀ t x r, L.AllowsAt t (select t x r)
  keeps : ∀ t x r, L.LegalAt t x → L.LegalAt (t+1) (select t x r).apply
attribute [instance] FiniteCoherentRealizer.finiteAlternatives

def nativeRealizer (active : Bool) : FiniteCoherentRealizer (nativeLaw active) where
  alternatives t := Branch (scheduled active ((nativeLaw active).score.opens t))
  select t x r := batch (scheduled active ((nativeLaw active).score.opens t)) x r
  weight t x r := coefficient (scheduled active ((nativeLaw active).score.opens t)) (pair x) r
  allows _t x r := batch_legal _ x r
  keeps _ _ _ _ _ hJ _ := False.elim (List.not_mem_nil hJ)

def realizerKernel (active : Bool) (t : ℕ) : Matrix Raw Raw ℚ := fun y x =>
  ∑ r : (nativeRealizer active).alternatives t,
    if pair ((nativeRealizer active).select t (table x) r).apply=y
    then (nativeRealizer active).weight t (table x) r else 0
lemma realizer_kernel (active : Bool) (t : ℕ) :
    realizerKernel active t=gateMatrix (scheduled active ((nativeLaw active).score.opens t)) := by
  funext y x
  exact branch_kernel _ x y
lemma native_tick (active : Bool) :
    realizerKernel active 2*realizerKernel active 1*realizerKernel active 0=tick active := by
  rw [realizer_kernel,realizer_kernel,realizer_kernel,tick_order]
  rfl


lemma realizer_periodic (active : Bool) (t : ℕ) :
    realizerKernel active (t+3)=realizerKernel active t := by
  rw [realizer_kernel,realizer_kernel]
  congr 2
  apply Fin.ext
  simp [nativeLaw]
lemma native_six (active : Bool) :
    realizerKernel active 5*realizerKernel active 4*realizerKernel active 3*
      realizerKernel active 2*realizerKernel active 1*realizerKernel active 0=
      compile (tickWord active++tickWord active) := by
  simp only [realizer_kernel]
  simp [nativeLaw,scheduled,tickWord,compile,gateMatrix,Matrix.mul_assoc]

lemma batch_ext {x : frame.Table} {b c : Batch frame x} (h : b.apps = c.apps) : b=c := by
  cases b with | mk a ha => cases c with | mk d hd => cases h; rfl
lemma admitted_electric (e : Bool) (x : frame.Table) (b : Batch frame x) :
    Admitted (.electric e) x b ↔ b.apps=[] ∨
      ∃ c : G, b.apps=[⟨replacement e c,trivial⟩] := by
  constructor
  · rintro ⟨r,rfl⟩
    cases r with
    | none => exact Or.inl rfl
    | some c => exact Or.inr ⟨c,rfl⟩
  · rintro (h|⟨c,h⟩)
    · exact ⟨none,batch_ext h.symm⟩
    · exact ⟨some c,batch_ext h.symm⟩
lemma admitted_curvature (active : Bool) (x : frame.Table) (b : Batch frame x) :
    Admitted (.curvature active) x b ↔ b.apps=[] ∨ b.apps=[⟨curvatureProfile,trivial⟩] := by
  constructor
  · rintro ⟨r,rfl⟩
    cases r with
    | none => exact Or.inl rfl
    | some u => exact Or.inr rfl
  · rintro (h|h)
    · exact ⟨none,batch_ext h.symm⟩
    · exact ⟨some (),batch_ext h.symm⟩
lemma batch_injective (g : Gate) (x : frame.Table) : Function.Injective (batch g x) := by
  intro r s h
  have hl := congrArg (fun b : Batch frame x => b.apps.length) h
  cases g with
  | curvature active =>
    cases r <;> cases s <;> simp_all [batch,emptyBatch,singleBatch]
  | electric e =>
    cases r with
    | none => cases s <;> simp_all [batch,emptyBatch,singleBatch]
    | some c =>
      cases s with
      | none => simp [batch,emptyBatch,singleBatch] at hl
      | some d =>
        have hv := congrArg (fun b : Batch frame x =>
          b.apps.head?.map (fun a => a.profile.update x (edge e))) h
        simpa [batch,singleBatch,replacement] using hv

lemma coefficient_reads (g : Gate) (x y : Raw) (r : Branch g)
    (h : ∀ a ∈ (batch g (table x) r).apps,
      ∀ p ∈ a.profile.reads, table x p = table y p) : coefficient g x r=coefficient g y r := by
  cases g with
  | curvature active =>
    cases r with
    | none => rfl
    | some u =>
      have he : table x=table y := by
        funext p
        exact h _ (List.mem_singleton_self _) p trivial
      have hx : x=y := by simpa only [pair_table] using congrArg pair he
      subst y
      rfl
  | electric e =>
    cases r with
    | none => rfl
    | some c =>
      have he := h _ (List.mem_singleton_self _) (edge e) (Set.mem_singleton _)
      simp only [coefficient,he]

/-! ## Non-vacuity -/
example : commit (.electric false) (elements 1,1) (some 1)=
    commit (.electric false) (1,1) (some 1) := by simp [commit_electric]
example : (batch (.electric false) (table (1,1)) (some 1)).apps.length=1 := rfl
example : (batch (.curvature false) (table (1,1)) (some ())).apps.length=1 := rfl
end Artform.Scores.Nonabelian
