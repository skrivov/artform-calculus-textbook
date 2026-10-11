import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card

/-!
# Histories: why WITNESS and SCRIPT are two roles

Section 4 of the paper. The policy cannot tell WITNESS from SCRIPT
(`witness_script_same_policy`). Their rules tell them apart: a script acts,
and a run is the list of its applications; evidence admits an application and
is counted as a property. This is the Type-theoretic view box of the
textbook's §7.4 (`qr:composition`): `App` holds moves, not proofs.

A law on labels `X` gives, for labels `y` and `z`, the finite type
`App y z` of its applications from `y` to `z` (SCRIPT data), and for each
application the finite type `Ev a` of its certificates (WITNESS data).

* `histories`: histories counted the book's way: one per list of admitted
  applications.
* `proofs`: each certificate counted as a value, as one role for both jobs
  would count it when certificates are counted like moves.
* `trajectories`: applications counted by their endpoints only, as one role
  for both jobs would count them when moves are counted like properties.
* `proofs_eq_histories`, `histories_eq_trajectories`: the counts agree when
  certificates, or applications, are unique.
* `twoCorners`: a law where the three counts are 3, 2 and 1.
-/

namespace Artform.Roles

open Finset

/-- A law's applications between labels, with the certificates of each. -/
structure Law (X : Type*) [Fintype X] where
  App : X → X → Type
  [appFintype : ∀ y z, Fintype (App y z)]
  Ev : {y z : X} → App y z → Type
  [evFintype : ∀ {y z} (a : App y z), Fintype (Ev a)]

attribute [instance] Law.appFintype Law.evFintype

namespace Law

variable {X : Type*} [Fintype X] [DecidableEq X] (L : Law X)

/-- Whether an application is admitted: it has a certificate. -/
def admitted {y z : X} (a : L.App y z) : ℕ :=
  if 0 < Fintype.card (L.Ev a) then 1 else 0

/-- The histories of `n` applications from `x₀` to `z`, each admitted
application counted once, whatever its certificates. -/
def histories (x₀ : X) : ℕ → X → ℕ
  | 0, z => if z = x₀ then 1 else 0
  | n + 1, z => ∑ y, ∑ a : L.App y z, L.admitted a * histories x₀ n y

/-- The same lists with every certificate counted as a value. -/
def proofs (x₀ : X) : ℕ → X → ℕ
  | 0, z => if z = x₀ then 1 else 0
  | n + 1, z => ∑ y, ∑ a : L.App y z, Fintype.card (L.Ev a) * proofs x₀ n y

/-- Whether some admitted application leads from `y` to `z`. -/
def step (y z : X) : ℕ :=
  if ∃ a : L.App y z, 0 < Fintype.card (L.Ev a) then 1 else 0

/-- The sequences of labels joined by admitted applications: applications
counted by their endpoints only. -/
def trajectories (x₀ : X) : ℕ → X → ℕ
  | 0, z => if z = x₀ then 1 else 0
  | n + 1, z => ∑ y, L.step y z * trajectories x₀ n y

/-- If every application has at most one certificate, counting certificates
changes nothing. -/
theorem proofs_eq_histories (h : ∀ {y z : X} (a : L.App y z), Fintype.card (L.Ev a) ≤ 1)
    (x₀ : X) : ∀ n z, L.proofs x₀ n z = L.histories x₀ n z := by
  intro n
  induction n with
  | zero => intro z; rfl
  | succ n ih =>
    intro z
    simp only [proofs, histories]
    refine sum_congr rfl fun y _ => sum_congr rfl fun a _ => ?_
    rw [ih y]
    congr 1
    have := h a
    unfold admitted
    split <;> omega

/-- If between two labels at most one application is admitted, counting
applications or endpoints gives the same number. -/
theorem histories_eq_trajectories
    (h : ∀ (y z : X) (a b : L.App y z),
      0 < Fintype.card (L.Ev a) → 0 < Fintype.card (L.Ev b) → a = b)
    (x₀ : X) : ∀ n z, L.histories x₀ n z = L.trajectories x₀ n z := by
  intro n
  induction n with
  | zero => intro z; rfl
  | succ n ih =>
    intro z
    simp only [histories, trajectories]
    refine sum_congr rfl fun y _ => ?_
    rw [ih y, ← sum_mul]
    congr 1
    unfold step admitted
    split_ifs with hex
    · obtain ⟨a, ha⟩ := hex
      rw [sum_eq_single a]
      · simp [ha]
      · intro b _ hb
        simp only [ite_eq_right_iff]
        intro hb'
        exact absurd (h y z b a hb' ha) hb
      · intro ha'; exact absurd (mem_univ a) ha'
    · refine sum_eq_zero fun a _ => ?_
      simp only [ite_eq_right_iff]
      intro ha; exact absurd ⟨a, ha⟩ hex

end Law

/-- Two corners joined by two moves: from either corner, stepping ahead or
stepping behind reaches the other corner. Stepping ahead has two
certificates, stepping behind one. The applications between two different
corners are numbered `0` (ahead) and `1` (behind). -/
def twoCorners : Law (Fin 2) where
  App y z := Fin (if y = z then 0 else 2)
  Ev a := Fin (if a.val = 0 then 2 else 1)

/-- One step from the first corner to the second: three certificate lists, two
histories, one trajectory. -/
theorem twoCorners_counts :
    twoCorners.proofs 0 1 1 = 3 ∧ twoCorners.histories 0 1 1 = 2 ∧
      twoCorners.trajectories 0 1 1 = 1 := by
  decide

end Artform.Roles
