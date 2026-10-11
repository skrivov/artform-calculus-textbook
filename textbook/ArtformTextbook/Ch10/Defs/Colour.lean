import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RepresentationTheory.Basic
import ArtformTextbook.Meta.Book

/-!
# Colour (Sections 10.3 and 10.4)

The colour space of one quark is `V = ℂ³` with basis `e₁, e₂, e₃` (here `e 0`, `e 1`, `e 2`).
Three quarks have colour states in `V ⊗ V ⊗ V`, written here as the third tensor power
`⨂[ℂ]^3 V`, whose basis states `e_a ⊗ e_b ⊗ e_c` are `⨂ₜ[ℂ] i, e (![a, b, c] i)`.

Definition 5.31 (the invariant vertex coupling, or intertwiner) is stated here, in the form in
which Proposition 10.1 uses it.
-/

namespace Artform

open scoped TensorProduct

/-- **Definition 5.31** (invariant vertex coupling). Let representations `ρ₁, …, ρₘ` of `G` act
on spaces `V₁, …, Vₘ`, the `k`th on the value `wₖ` arriving at a vertex. An *intertwiner* at the
vertex is a function `ι(w₁, …, wₘ) ∈ ℂ`, linear in each argument, such that
`ι(ρ₁(g)w₁, …, ρₘ(g)wₘ) = ι(w₁, …, wₘ)` for every `g ∈ G` and all `wₖ ∈ Vₖ`. The
arguments are numbered `0, …, m - 1`. -/
@[book "def:intertwiner"]
def IsIntertwiner {G : Type*} [Monoid G] {m : ℕ} {V : Fin m → Type*}
    [∀ k, AddCommGroup (V k)] [∀ k, Module ℂ (V k)]
    (ρ : ∀ k, Representation ℂ G (V k)) (ι : MultilinearMap ℂ V ℂ) : Prop :=
  ∀ (g : G) (w : ∀ k, V k), ι (fun k => ρ k g (w k)) = ι w

namespace Colour

/-- The basis vector `e_a` of the colour space `V = ℂ³`. -/
def e (a : Fin 3) : Fin 3 → ℂ := Pi.single a 1

/-- The colourless three-quark state
`ε = Σ_{σ ∈ S₃} sgn(σ) e_{σ(1)} ⊗ e_{σ(2)} ⊗ e_{σ(3)}` in `V ⊗ V ⊗ V`. -/
noncomputable def epsilon : ⨂[ℂ]^3 (Fin 3 → ℂ) :=
  ∑ σ : Equiv.Perm (Fin 3), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ⨂ₜ[ℂ] i, e (σ i)

/-- The action `g ⊗ g ⊗ g` of a matrix `g` on `V ⊗ V ⊗ V`, where `g` acts on `V` by
`g e_a = Σ_b g_{ba} e_b`. -/
noncomputable def tensorCube (g : Matrix (Fin 3) (Fin 3) ℂ) :
    ⨂[ℂ]^3 (Fin 3 → ℂ) →ₗ[ℂ] ⨂[ℂ]^3 (Fin 3 → ℂ) :=
  PiTensorProduct.map fun _ => Matrix.toLin' g

/-- Contraction with `ε`: the trilinear function
`ι(w₁, w₂, w₃) = Σ_{a,b,c} ε_{abc} w₁ᵃ w₂ᵇ w₃ᶜ = Σ_{σ ∈ S₃} sgn(σ) w₁^{σ(1)} w₂^{σ(2)} w₃^{σ(3)}`,
where `ε_{abc}` is the coefficient of `ε` on `e_a ⊗ e_b ⊗ e_c`. -/
noncomputable def contraction : MultilinearMap ℂ (fun _ : Fin 3 => Fin 3 → ℂ) ℂ :=
  ∑ σ : Equiv.Perm (Fin 3), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
    (MultilinearMap.mkPiAlgebra ℂ (Fin 3) ℂ).compLinearMap fun i => LinearMap.proj (σ i)

/-- The triplet of a group `G ≤ GL(3, ℂ)`: each element acts on `V = ℂ³` by its matrix. -/
noncomputable def triplet (G : Subgroup (GL (Fin 3) ℂ)) : Representation ℂ G (Fin 3 → ℂ) where
  toFun g := Matrix.toLin' ((g : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Matrix.toLin'_mul, Module.End.mul_eq_comp]

/-- `ω = e^{2πi/3}`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

/-- The colour states of `q` quarks and `q̄` antiquarks, `V^{⊗q} ⊗ V̄^{⊗q̄}`. As a space the
conjugate triplet `V̄` is again `ℂ³`, with basis `ē_a`; only the action differs. -/
abbrev QuarkStates (q qbar : ℕ) : Type :=
  (⨂[ℂ]^q (Fin 3 → ℂ)) ⊗[ℂ] (⨂[ℂ]^qbar (Fin 3 → ℂ))

/-- The action of a matrix `g` on states of `q` quarks and `q̄` antiquarks: by `g` on each
quark factor `V`, and by the complex conjugate matrix `ḡ` on each antiquark factor `V̄`
(the conjugate `w̄` of a value `w` lies in the conjugate representation, so `g w` has
conjugate `ḡ w̄`). -/
noncomputable def act (q qbar : ℕ) (g : Matrix (Fin 3) (Fin 3) ℂ) :
    QuarkStates q qbar →ₗ[ℂ] QuarkStates q qbar :=
  TensorProduct.map (PiTensorProduct.map fun _ => Matrix.toLin' g)
    (PiTensorProduct.map fun _ => Matrix.toLin' (g.map (starRingEnd ℂ)))

end Colour

end Artform
