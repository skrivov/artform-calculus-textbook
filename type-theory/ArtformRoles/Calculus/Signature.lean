import ArtformRoles.Calculus.Syntax
import ArtformRoles.Calculus.Effect

/-!
# Signatures, contexts and policy validity

Sections 6.1, 6.3 and 6.4 of the paper.

* A signature is a list of entries (§6.4): a family `a : (Δ) ⇒_ρ Type`, a
  primitive `c :_ρ A`, a certificate bundle `d = (a_d, e_d, o_d) : A` at role
  `σ`, an exact attestation `q@t = (e_q, o_q) : A`, and a gate
  `g : Δ; Stamped_σ(A) ⇒_ρ B`. Entries are named by their position, so names
  are fresh and a later entry cannot rename an earlier one.
* A context lists its variables nearest first: `Γ[i]` declares `var i`.
* `roleOf S Γ z` is the role of an atom: a variable's declared role, a family's
  or gate's result role, a constant's role.
* `Valid S Γ ρ ε` is Definition 6.1 (policy-valid effect):
  `D(role(z), ρ) ≤ ε(z)` for every atom `z` of `S` and `Γ`.
* `Tel.inst t Δ` puts `t` for the first entry of a telescope in the later
  entries; `instType ds Δ C` instantiates a type `C` under the whole telescope
  with the arguments `ds`, as in `A[d⃗]` and `B[d⃗]` of the gate rules.
-/

namespace Artform.Roles.Calculus

open Exp

/-- A telescope: its entries in order, each type in the context of the earlier
entries (the nearest earlier entry is `var 0`). -/
abbrev Tel := List (Role × Exp)

/-- A context: its declarations nearest first; `Γ[i]` declares `var i`, and its
type lives in the context `Γ.drop (i + 1)`. -/
abbrev Ctx := List (Role × Exp)

/-- An entry of a signature (§6.4). -/
inductive Entry
  /-- A family `a : (Δ) ⇒_ρ Type`. -/
  | family (Δ : Tel) (ρ : Role)
  /-- A primitive `c :_ρ A`. -/
  | prim (ρ : Role) (A : Exp)
  /-- A certificate bundle `d = (a_d, e_d, o_d) : A` with payload role `σ`. -/
  | cert (σ : Role) (A : Exp)
  /-- An exact attestation `q@t = (e_q, o_q) : A`. -/
  | attest (A t : Exp)
  /-- A gate `g : Δ; Stamped_σ(A) ⇒_ρ B`, with its private node former. -/
  | gate (Δ : Tel) (σ : Role) (A : Exp) (ρ : Role) (B : Exp)
  deriving DecidableEq, Repr

/-- A signature: a finite ordered list of entries. -/
abbrev Sig := List Entry

namespace Sig

/-- The family declared at position `a`. -/
def family? (S : Sig) (a : ℕ) : Option (Tel × Role) :=
  match S[a]? with
  | some (.family Δ ρ) => some (Δ, ρ)
  | _ => none

/-- The gate declared at position `g`. -/
def gate? (S : Sig) (g : ℕ) : Option (Tel × Role × Exp × Role × Exp) :=
  match S[g]? with
  | some (.gate Δ σ A ρ B) => some (Δ, σ, A, ρ, B)
  | _ => none

/-- The role and type of the public constant `const i k`. A certificate's
origin has type `Origin_A(e_d, a_d)`, an attestation's `Origin_A(e_q, t)`. -/
def const? (S : Sig) (i k : ℕ) : Option (Role × Exp) :=
  match S[i]?, k with
  | some (.prim ρ A), 0 => some (ρ, A)
  | some (.cert σ A), 0 => some (σ, A)
  | some (.cert _ _), 1 => some (.witness, .event)
  | some (.cert _ A), 2 => some (.witness, .origin A (.const i 1) (.const i 0))
  | some (.attest _ _), 0 => some (.witness, .event)
  | some (.attest A t), 1 => some (.witness, .origin A (.const i 0) t)
  | _, _ => none

/-- The role of the public declaration atom `decl i k`. -/
def declRole? (S : Sig) (i k : ℕ) : Option Role :=
  match S[i]?, k with
  | some (.family _ ρ), 0 => some ρ
  | some (.gate _ _ _ ρ _), 0 => some ρ
  | _, _ => (S.const? i k).map Prod.fst

end Sig

/-- The role of an atom of the signature `S` and the context `Γ`. -/
def roleOf (S : Sig) (Γ : Ctx) : Atom → Option Role
  | .var i => (Γ[i]?).map Prod.fst
  | .decl i k => S.declRole? i k

/-- Definition 6.1: an effect at result role `ρ` is policy valid when every atom
of role `σ` has grade at least `D(σ, ρ)`. -/
def Valid (S : Sig) (Γ : Ctx) (ρ : Role) (ε : Eff) : Prop :=
  ∀ z r, roleOf S Γ z = some r → demand r ρ ≤ ε z

/-- Put `t` for the variable of a telescope's first entry in a type that lies
under `k` later entries. -/
def instAt (t : Exp) (k : ℕ) (C : Exp) : Exp := C.subst (upN k (inst1 t))

/-- Substitute in a telescope: each later entry lies under one more binder. -/
def Tel.subst : (ℕ → Exp) → Tel → Tel
  | _, [] => []
  | σ, (ρ, A) :: Δ => (ρ, A.subst σ) :: Tel.subst (up σ) Δ

/-- Instantiate the first entry of a telescope by `t` in the later entries. -/
def Tel.inst (t : Exp) (Δ : Tel) : Tel := Tel.subst (inst1 t) Δ

/-- Instantiate a type lying under the whole telescope `Δ` by the arguments
`ds` (a `cons` list, first argument first). -/
def instType : Exp → Tel → Exp → Exp
  | .cons t ts, _ :: Δ, C => instType ts (Tel.inst t Δ) (instAt t Δ.length C)
  | _, _, C => C

/-! ## Syntactic classes of §6.3 -/

namespace Exp

/-- `gradefree A`: every grade of a dependent function type occurring anywhere
in `A` is `0`. -/
def gradefree : Exp → Prop
  | var _ => True
  | const _ _ => True
  | fam _ args => gradefree args
  | event => True
  | origin A e t => gradefree A ∧ gradefree e ∧ gradefree t
  | stamped _ A => gradefree A
  | pi q _ A B => q = .free ∧ gradefree A ∧ gradefree B
  | sigma _ A B => gradefree A ∧ gradefree B
  | lam _ _ A t => gradefree A ∧ gradefree t
  | app t u => gradefree t ∧ gradefree u
  | pair t u => gradefree t ∧ gradefree u
  | fst t => gradefree t
  | snd t => gradefree t
  | stamp t e o => gradefree t ∧ gradefree e ∧ gradefree o
  | gate _ ds s => gradefree ds ∧ gradefree s
  | node _ _ ds t e => gradefree ds ∧ gradefree t ∧ gradefree e
  | nil => True
  | cons t ts => gradefree t ∧ gradefree ts

/-- `public t`: `t` contains no private node. -/
def IsPublic : Exp → Prop
  | var _ => True
  | const _ _ => True
  | fam _ args => IsPublic args
  | event => True
  | origin A e t => IsPublic A ∧ IsPublic e ∧ IsPublic t
  | stamped _ A => IsPublic A
  | pi _ _ A B => IsPublic A ∧ IsPublic B
  | sigma _ A B => IsPublic A ∧ IsPublic B
  | lam _ _ A t => IsPublic A ∧ IsPublic t
  | app t u => IsPublic t ∧ IsPublic u
  | pair t u => IsPublic t ∧ IsPublic u
  | fst t => IsPublic t
  | snd t => IsPublic t
  | stamp t e o => IsPublic t ∧ IsPublic e ∧ IsPublic o
  | gate _ ds s => IsPublic ds ∧ IsPublic s
  | node .. => False
  | nil => True
  | cons t ts => IsPublic t ∧ IsPublic ts

/-- The result of a type after its outer dependent function binders. -/
def resultHead : Exp → Exp
  | pi _ _ _ B => resultHead B
  | A => A

end Exp

/-- `ordinaryHead(A)`: after the outer dependent function binders, the result
head is a declared family. -/
def OrdinaryHead (S : Sig) (A : Exp) : Prop :=
  ∃ a args, A.resultHead = .fam a args ∧ (S.family? a).isSome

/-- `wdata(A)` (rule WitnessData): witness-family applications and homogeneous
witness sums of them. -/
inductive WData (S : Sig) : Exp → Prop
  | fam {a args Δ} : S.family? a = some (Δ, .witness) → WData S (.fam a args)
  | sigma {A B} : WData S A → WData S B → WData S (.sigma .witness A B)

end Artform.Roles.Calculus
