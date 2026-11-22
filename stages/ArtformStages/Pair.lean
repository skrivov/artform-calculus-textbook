import Mathlib

/-!
# Pair: a kick, then a drift

The law of light in the research ledger on a layered universe is *Pair*: on a state `(A, E)`,
with `A` on the lines and `E` on the dual lines, the *kick* adds `S A` to `E`, and then the
*drift* takes `L E'` from `A`, with the new `E'`:

  `E' = E + S A`,  `A' = A - L E'`.

In the ledger's wave 39 (astra's) `S = Cᵀ K C`, with `C` the edge of a square, and `K`, `L` the
weights. Its dossier holds the laws below by scripts and by arguments on paper; here they are
proved over any commutative ring `R` and any finite sets of cells, with no division, no
positivity and no size of the board.

* `pair_eq_drift_kick`, `unpair_pair`, `pair_unpair` (PA1): Pair is the drift after the kick,
  and `unpair` undoes it on both sides, for every `S` and `L`.
* `omega_pair` (PA2): with `S` and `L` symmetric, Pair keeps the alternating pairing
  `Ω((A, E), (B, F)) = A ⬝ F - E ⬝ B`.
* `qstar_pair` (PA3): with `S` and `L` symmetric, Pair keeps the staggered invariant
  `Q⋆(A, E) = A ⬝ S A + E ⬝ L E + A ⬝ S (L E)`.
* `pair_gauge`, `charge_pair` (PA4): with `S = Cᵀ K C` and `C D = 0`, Pair passes the gauge,
  `A + D g` going to `A' + D g`, and keeps the charge `Dᵀ E`.
* `pair_map`, `coeff_periodize`, `periodize_antipode`, `periodize_pair` (PA5): Pair commutes
  with every map of rings; periodization of fillings along a map of spaces is one, summing over
  each fiber; it commutes with turning a filling over; so it sends the Pair built from tables
  of stencils to the Pair built from their periodizations.

None of this is new: it is the linear algebra of a symplectic splitting of a quadratic
energy, and the functoriality of group rings.
-/

open Matrix MonoidAlgebra

namespace Artform.Stages

section Laws

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n]

/-- A state of light: `A` on the lines, `E` on the dual lines. -/
abbrev LightState (R n : Type*) := (n → R) × (n → R)

/-- **The kick**: `E` gains `S A`. -/
def kick (S : Matrix n n R) (x : LightState R n) : LightState R n :=
  (x.1, x.2 + S *ᵥ x.1)

/-- **The drift**: `A` loses `L E`. -/
def drift (L : Matrix n n R) (x : LightState R n) : LightState R n :=
  (x.1 - L *ᵥ x.2, x.2)

/-- **Pair**: the kick, then the drift. -/
def pair (S L : Matrix n n R) (x : LightState R n) : LightState R n :=
  (x.1 - L *ᵥ (x.2 + S *ᵥ x.1), x.2 + S *ᵥ x.1)

/-- Pair undone: undrift, then unkick. -/
def unpair (S L : Matrix n n R) (y : LightState R n) : LightState R n :=
  (y.1 + L *ᵥ y.2, y.2 - S *ᵥ (y.1 + L *ᵥ y.2))

/-- PA1. Pair is the drift after the kick. -/
theorem pair_eq_drift_kick (S L : Matrix n n R) (x : LightState R n) :
    pair S L x = drift L (kick S x) := rfl

/-- PA1. `unpair` undoes Pair. -/
theorem unpair_pair (S L : Matrix n n R) (x : LightState R n) : unpair S L (pair S L x) = x := by
  obtain ⟨A, E⟩ := x
  simp [pair, unpair]

/-- PA1. Pair undoes `unpair`. -/
theorem pair_unpair (S L : Matrix n n R) (y : LightState R n) : pair S L (unpair S L y) = y := by
  obtain ⟨A, E⟩ := y
  simp [pair, unpair]

/-- A symmetric table can be read from either side. -/
theorem dotProduct_mulVec_symm (M : Matrix n n R) (hM : Mᵀ = M) (v w : n → R) :
    v ⬝ᵥ (M *ᵥ w) = w ⬝ᵥ (M *ᵥ v) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]

/-- The same, with the table on the left. -/
theorem mulVec_dotProduct_symm (M : Matrix n n R) (hM : Mᵀ = M) (v w : n → R) :
    (M *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (M *ᵥ w) := by
  rw [dotProduct_comm, dotProduct_mulVec_symm M hM]

/-- The alternating pairing of two states. -/
def omega (x y : LightState R n) : R := x.1 ⬝ᵥ y.2 - x.2 ⬝ᵥ y.1

/-- A kick by a symmetric table keeps the pairing. -/
theorem omega_kick (S : Matrix n n R) (hS : Sᵀ = S) (x y : LightState R n) :
    omega (kick S x) (kick S y) = omega x y := by
  obtain ⟨A, E⟩ := x
  obtain ⟨B, F⟩ := y
  simp only [omega, kick, dotProduct_add, add_dotProduct]
  rw [dotProduct_mulVec_symm S hS A B, mulVec_dotProduct_symm S hS A B,
    dotProduct_mulVec_symm S hS A B]
  ring

/-- A drift by a symmetric table keeps the pairing. -/
theorem omega_drift (L : Matrix n n R) (hL : Lᵀ = L) (x y : LightState R n) :
    omega (drift L x) (drift L y) = omega x y := by
  obtain ⟨A, E⟩ := x
  obtain ⟨B, F⟩ := y
  simp only [omega, drift, dotProduct_sub, sub_dotProduct]
  rw [mulVec_dotProduct_symm L hL E F]
  ring

/-- PA2. With `S` and `L` symmetric, Pair keeps the alternating pairing. -/
theorem omega_pair (S L : Matrix n n R) (hS : Sᵀ = S) (hL : Lᵀ = L) (x y : LightState R n) :
    omega (pair S L x) (pair S L y) = omega x y := by
  rw [pair_eq_drift_kick, pair_eq_drift_kick, omega_drift L hL, omega_kick S hS]

/-- The staggered invariant, astra's `Q⋆ = 2 H⋆`. -/
def qstar (S L : Matrix n n R) (x : LightState R n) : R :=
  x.1 ⬝ᵥ (S *ᵥ x.1) + x.2 ⬝ᵥ (L *ᵥ x.2) + x.1 ⬝ᵥ (S *ᵥ (L *ᵥ x.2))

/-- PA3. With `S` and `L` symmetric, Pair keeps the staggered invariant. -/
theorem qstar_pair (S L : Matrix n n R) (hS : Sᵀ = S) (hL : Lᵀ = L) (x : LightState R n) :
    qstar S L (pair S L x) = qstar S L x := by
  obtain ⟨A, E⟩ := x
  simp only [qstar, pair]
  generalize hE' : E + S *ᵥ A = E'
  have h1 : A - L *ᵥ E' + L *ᵥ E' = A := sub_add_cancel _ _
  have h2 : E' - S *ᵥ A = E := by rw [← hE', add_sub_cancel_right]
  calc (A - L *ᵥ E') ⬝ᵥ (S *ᵥ (A - L *ᵥ E')) + E' ⬝ᵥ (L *ᵥ E')
          + (A - L *ᵥ E') ⬝ᵥ (S *ᵥ (L *ᵥ E'))
        = (A - L *ᵥ E') ⬝ᵥ (S *ᵥ (A - L *ᵥ E' + L *ᵥ E')) + E' ⬝ᵥ (L *ᵥ E') := by
          rw [mulVec_add, dotProduct_add]; ring
      _ = (A - L *ᵥ E') ⬝ᵥ (S *ᵥ A) + E' ⬝ᵥ (L *ᵥ E') := by rw [h1]
      _ = A ⬝ᵥ (S *ᵥ A) - E' ⬝ᵥ (L *ᵥ (S *ᵥ A)) + E' ⬝ᵥ (L *ᵥ E') := by
          rw [sub_dotProduct, mulVec_dotProduct_symm L hL]
      _ = A ⬝ᵥ (S *ᵥ A) + E' ⬝ᵥ (L *ᵥ (E' - S *ᵥ A)) := by
          rw [mulVec_sub, dotProduct_sub]; ring
      _ = A ⬝ᵥ (S *ᵥ A) + E' ⬝ᵥ (L *ᵥ E) := by rw [h2]
      _ = A ⬝ᵥ (S *ᵥ A) + E ⬝ᵥ (L *ᵥ E) + A ⬝ᵥ (S *ᵥ (L *ᵥ E)) := by
          rw [← hE', add_dotProduct, mulVec_dotProduct_symm S hS]; ring

variable {f v : Type*} [Fintype f] [Fintype v]

/-- PA4. With `S = Cᵀ K C` and `C D = 0`, Pair passes the gauge: a change `D g` of `A` at the
corners comes out as the same change, and `E` does not see it. -/
theorem pair_gauge (C : Matrix f n R) (D : Matrix n v R) (K : Matrix f f R) (L : Matrix n n R)
    (hCD : C * D = 0) (A E : n → R) (g : v → R) :
    pair (Cᵀ * K * C) L (A + D *ᵥ g, E) =
      ((pair (Cᵀ * K * C) L (A, E)).1 + D *ᵥ g, (pair (Cᵀ * K * C) L (A, E)).2) := by
  have h0 : (Cᵀ * K * C) *ᵥ (D *ᵥ g) = 0 := by
    rw [mulVec_mulVec, Matrix.mul_assoc, hCD, Matrix.mul_zero, zero_mulVec]
  simp only [pair, mulVec_add, h0, add_zero, Prod.mk.injEq, and_true]
  abel

omit [Fintype v] in
/-- PA4. With `S = Cᵀ K C` and `C D = 0`, Pair keeps the charge `Dᵀ E`. -/
theorem charge_pair (C : Matrix f n R) (D : Matrix n v R) (K : Matrix f f R) (L : Matrix n n R)
    (hCD : C * D = 0) (x : LightState R n) :
    Dᵀ *ᵥ (pair (Cᵀ * K * C) L x).2 = Dᵀ *ᵥ x.2 := by
  have h0 : Dᵀ * (Cᵀ * K * C) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hCD, Matrix.transpose_zero,
      Matrix.zero_mul, Matrix.zero_mul]
  simp only [pair, mulVec_add, mulVec_mulVec, h0, zero_mulVec, add_zero]

end Laws

section Periodization

variable {R R' : Type*} [CommRing R] [CommRing R'] {n : Type*} [Fintype n]

/-- A map of rings applied to every number of a state. -/
def mapState (h : R →+* R') (x : LightState R n) : LightState R' n := (h ∘ x.1, h ∘ x.2)

theorem comp_mulVec (h : R →+* R') (M : Matrix n n R) (w : n → R) :
    h ∘ (M *ᵥ w) = M.map h *ᵥ (h ∘ w) :=
  funext fun i => RingHom.map_mulVec h M w i

/-- PA5(a). Pair commutes with every map of rings, applied to its tables and its state. -/
theorem pair_map (h : R →+* R') (S L : Matrix n n R) (x : LightState R n) :
    mapState h (pair S L x) = pair (S.map h) (L.map h) (mapState h x) := by
  obtain ⟨A, E⟩ := x
  have hsub : ∀ a b : n → R, h ∘ (a - b) = h ∘ a - h ∘ b := fun a b => funext fun i => map_sub h _ _
  have hadd : ∀ a b : n → R, h ∘ (a + b) = h ∘ a + h ∘ b := fun a b => funext fun i => map_add h _ _
  simp only [mapState, pair, hsub, hadd, comp_mulVec]

variable {G H : Type*}

/-- PA5(b). Periodization along a map of spaces `p`, at a law `b` of the quotient, is the sum of
the values at the laws that `p` sends to `b`. -/
theorem coeff_periodize [Monoid G] [Monoid H] [DecidableEq H] (p : G →* H) (x : R[G]) (b : H) :
    (mapDomainRingHom R p x).coeff b = ∑ g ∈ x.coeff.support with p g = b, x.coeff g := by
  rw [Finset.sum_filter]
  simp only [mapDomainRingHom_apply, MonoidAlgebra.mapDomain, coeff_ofCoeff,
    Finsupp.mapDomain_apply, Finsupp.sum, Finsupp.single_apply]

/-- Turning a filling over: every law to its inverse. On a space whose rows pass, a map of rings. -/
noncomputable abbrev turnOver (R G : Type*) [CommRing R] [CommGroup G] : R[G] →+* R[G] :=
  mapDomainRingHom R (invMonoidHom (α := G))

/-- PA5(c). Periodization commutes with turning over. -/
theorem periodize_antipode [CommGroup G] [CommGroup H] (p : G →* H) :
    (mapDomainRingHom R p).comp (turnOver R G) = (turnOver R H).comp (mapDomainRingHom R p) := by
  rw [← mapDomainRingHom_comp, ← mapDomainRingHom_comp]
  congr 1
  ext g
  simp

/-- The table turned over: the edge of a square read back, as `Cᵀ` is on a board. -/
noncomputable def turned {f : Type*} [CommGroup G] (C : Matrix f n R[G]) : Matrix n f R[G] :=
  (C.map (turnOver R G))ᵀ

/-- PA5(d). Periodization sends the Pair built from the tables of stencils `C`, `K` and `L` to
the Pair built from their periodizations: astra's square `P T(plane) = T(quotient) P`. -/
theorem periodize_pair {f : Type*} [Fintype f] [CommGroup G] [CommGroup H] (p : G →* H)
    (C : Matrix f n R[G]) (K : Matrix f f R[G]) (L : Matrix n n R[G]) (x : LightState R[G] n) :
    mapState (mapDomainRingHom R p) (pair (turned C * K * C) L x) =
      pair (turned (C.map (mapDomainRingHom R p)) * K.map (mapDomainRingHom R p) *
        C.map (mapDomainRingHom R p)) (L.map (mapDomainRingHom R p))
        (mapState (mapDomainRingHom R p) x) := by
  rw [pair_map, Matrix.map_mul, Matrix.map_mul]
  congr 3
  simp only [turned, transpose_map, Matrix.map_map]
  congr 2
  exact congrArg DFunLike.coe (periodize_antipode p)

end Periodization

end Artform.Stages
