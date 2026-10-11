import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import ArtformTextbook.Ch11.Defs.Colourless
import ArtformTextbook.Ch11.Defs.Response

/-!
# The hop, its coin, and a native tick (Section 11.6)

On one edge `x → y` (`Ch11/Defs/Colourless.lean`), a quark at `x` with colour `c'` arrives at
`y` with colour `c` and coefficient `U_{cc'}`, the entry of the matrix `ρ(U)` of the link
value. The hop at the link value `U` is the operator `V_U` on the coefficient tables over the
occupations, and the hop of the edge applies `V_U` at every link value, `V = ⊕_U V_U`.

The coin is built on the one-quark modes, `x` first: `K_U = [[0, U†], [U, 0]] ⊗ 1_d`, the hop
of one quark, and `W_U = (1 + i K_U)/√2`. The many-quark coin is the second quantization
`Γ(W_U)` (`Fock.secondQuant`), the coin of the edge is `𝒞 = ⊕_U Γ(W_U)`, and the tick is
`T = 𝒞 𝒦`, `𝒦` the electric read of Definition 11.7. The family of coins `Γ(e^{iθ K_U})`
uses the matrix exponential `NormedSpace.exp`.

`A_{cc'} = Σ_s a†_{ycs} a_{xc's}` and the there-and-back tally `Ω` are those of
Theorem 11.20.

Every operator here is a matrix indexed by occupation tables, entry `(n', n)` being the
coefficient of `|n'⟩` in the image of `|n⟩`; operators on the states of the edge act at each
link value, or on the link (the read).
-/

namespace Artform

namespace Edge

open scoped Matrix ComplexConjugate

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

/-- The hop `V_U` at the link value with matrix `U`:
`V_U = Σ_{c,c',s} U_{cc'} a†_{ycs} a_{xc's} + h.c.`, where
`h.c. = Σ_{c,c',s} conj(U_{cc'}) a†_{xc's} a_{ycs}` is the hop back with the inverse link. -/
noncomputable def hopAt (ord : LinearOrder (Mode C S)) (U : Matrix C C ℂ) :
    Matrix (Finset (Mode C S)) (Finset (Mode C S)) ℂ :=
  (∑ c, ∑ c', ∑ s, U c c' •
      (Fock.creation ord (Sum.inr (c, s)) * Fock.annihilation ord (Sum.inl (c', s)))) +
    ∑ c, ∑ c', ∑ s, conj (U c c') •
      (Fock.creation ord (Sum.inl (c', s)) * Fock.annihilation ord (Sum.inr (c, s)))

variable {G : Type*} [Group G]

/-- The hop of the edge, `V = ⊕_U V_U`: it applies `V_U` at every link value, diagonal in
`U`, `(V ψ)(U) = V_U ψ(U)`. -/
noncomputable def hop (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S))
    (ψ : G → Finset (Mode C S) → ℂ) : G → Finset (Mode C S) → ℂ :=
  fun U => hopAt ord (ρ U) *ᵥ ψ U

/-- The hop of one quark, `K_U = [[0, U†], [U, 0]] ⊗ 1_d` on the one-quark modes of the edge,
`x` first: a quark at `x` with colour `c'` goes to `y` with colour `c` and coefficient
`U_{cc'}`, and a quark at `y` returns through `U†`. -/
def coinK (U : Matrix C C ℂ) : Matrix (Mode C S) (Mode C S) ℂ :=
  Matrix.fromBlocks 0 (Matrix.kroneckerMap (· * ·) (star U) (1 : Matrix S S ℂ))
    (Matrix.kroneckerMap (· * ·) U (1 : Matrix S S ℂ)) 0

/-- The coin of one quark, `W_U = (1 + i K_U)/√2`. -/
noncomputable def coinW (U : Matrix C C ℂ) : Matrix (Mode C S) (Mode C S) ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (1 + Complex.I • coinK U)

/-- The coin of the edge, `𝒞 = ⊕_U Γ(W_U)`: at each link value `U`, the second quantization of
the coin `W_U` over all modes of the edge, `(𝒞 ψ)(U) = Γ(W_U) ψ(U)`. -/
noncomputable def coin (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S))
    (ψ : G → Finset (Mode C S) → ℂ) : G → Finset (Mode C S) → ℂ :=
  fun U => Fock.secondQuant ord (coinW (ρ U)) *ᵥ ψ U

/-- The tick `T = 𝒞 𝒦` (`eq:mt-tick`): the electric read `𝒦` of the response `r`
(Definition 11.7), then the coin `𝒞`. -/
noncomputable def tick [Fintype G] (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S))
    {ι : Type*} [Fintype ι] {d : ι → ℕ} (σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ))
    (r : ι → ℂ) (ψ : G → Finset (Mode C S) → ℂ) : G → Finset (Mode C S) → ℂ :=
  coin ρ ord (electricRead σ r ψ)

/-- The family of coins of the edge, `𝒞_θ = ⊕_U Γ(e^{iθ K_U})`, with the matrix exponential. -/
noncomputable def coinFamily (ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Mode C S)) (θ : ℝ)
    (ψ : G → Finset (Mode C S) → ℂ) : G → Finset (Mode C S) → ℂ :=
  fun U => Fock.secondQuant ord (NormedSpace.exp (((θ : ℂ) * Complex.I) • coinK (ρ U))) *ᵥ ψ U

/-- `A_{cc'} = Σ_s a†_{ycs} a_{xc's}`: the hop of one quark from colour `c'` at `x` to colour `c`
at `y`, summed over the slots. -/
noncomputable def hopA (ord : LinearOrder (Mode C S)) (c c' : C) :
    Matrix (Finset (Mode C S)) (Finset (Mode C S)) ℂ :=
  ∑ s, Fock.creation ord (Sum.inr (c, s)) * Fock.annihilation ord (Sum.inl (c', s))

/-- The there-and-back tally of Theorem 11.20,
`Ω = (1/3) Σ_{c,c'} (A†_{cc'} A_{cc'} + A_{cc'} A†_{cc'})
  + (m/3) Σ_{c,c'} (A_{cc'} A_{cc'} + A†_{cc'} A†_{cc'})`. -/
noncomputable def tally (ord : LinearOrder (Mode C S)) (m : ℕ) :
    Matrix (Finset (Mode C S)) (Finset (Mode C S)) ℂ :=
  (1 / 3 : ℂ) • (∑ c, ∑ c',
      ((hopA ord c c')ᴴ * hopA ord c c' + hopA ord c c' * (hopA ord c c')ᴴ)) +
    ((m : ℂ) / 3) • (∑ c, ∑ c',
      (hopA ord c c' * hopA ord c c' + (hopA ord c c')ᴴ * (hopA ord c c')ᴴ))

/-- An operator on the coefficient tables over the occupations, applied to a state at every link
value: `(X ψ)(U) = X ψ(U)`. -/
def atEachLink (X : Matrix (Finset (Mode C S)) (Finset (Mode C S)) ℂ)
    (ψ : G → Finset (Mode C S) → ℂ) : G → Finset (Mode C S) → ℂ :=
  fun U => X *ᵥ ψ U

/-- The invariants of `3^{⊗3}`: the tensors `T ∈ ℂ³ ⊗ ℂ³ ⊗ ℂ³`, given by their components
`T_{jln}`, fixed by `U ⊗ U ⊗ U` for every `U ∈ G`:
`Σ_{j,l,n} U_{ij} U_{kl} U_{mn} T_{jln} = T_{ikm}`. -/
def tripleInvariants (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) :
    Submodule ℂ (Fin 3 → Fin 3 → Fin 3 → ℂ) where
  carrier := {T | ∀ U, (fun i k m => ∑ j, ∑ l, ∑ n, ρ U i j * ρ U k l * ρ U m n * T j l n) = T}
  add_mem' {T T'} hT hT' U := by
    simp only [Set.mem_ofPred_eq] at hT hT'
    funext i k m
    have h1 : ∑ j, ∑ l, ∑ n, ρ U i j * ρ U k l * ρ U m n * T j l n = T i k m :=
      congrFun (congrFun (congrFun (hT U) i) k) m
    have h2 : ∑ j, ∑ l, ∑ n, ρ U i j * ρ U k l * ρ U m n * T' j l n = T' i k m :=
      congrFun (congrFun (congrFun (hT' U) i) k) m
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, h1, h2]
  zero_mem' U := by
    funext i k m
    simp
  smul_mem' c T hT U := by
    simp only [Set.mem_ofPred_eq] at hT
    funext i k m
    have h1 : ∑ j, ∑ l, ∑ n, ρ U i j * ρ U k l * ρ U m n * T j l n = T i k m :=
      congrFun (congrFun (congrFun (hT U) i) k) m
    simp only [Pi.smul_apply, smul_eq_mul, ← h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun n _ => ?_
    ring

end Edge

/-- The Levi-Civita symbol `ε_{ikm}`: the sign of the permutation `(i, k, m)` of the three
colours, and zero when two indices agree. It is the coefficient of
`ε = Σ_σ sgn(σ) e_{σ(1)} ⊗ e_{σ(2)} ⊗ e_{σ(3)}` (Proposition 10.1) on `e_i ⊗ e_k ⊗ e_m`. -/
def leviCivita (i k m : Fin 3) : ℂ :=
  ∑ σ : Equiv.Perm (Fin 3),
    if σ 0 = i ∧ σ 1 = k ∧ σ 2 = m then ((Equiv.Perm.sign σ : ℤ) : ℂ) else 0

end Artform
