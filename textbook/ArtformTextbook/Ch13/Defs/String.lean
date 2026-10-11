import ArtformTextbook.Ch05.Defs.Curvature
import ArtformTextbook.Ch11.Colourless
import ArtformTextbook.Ch11.Defs.Energy
import ArtformTextbook.Ch12.Defs.ColourGroups

/-!
# A flux string (Section 13.1)

The canvas is a path of `R` edges, `x₀ → x₁ → ⋯ → x_R` (`Canvas.path`), whose link values
`U_1, …, U_R` form a link table of its transport skeleton (Definition 5.19); the book's link
`U_{j+1}` is the value on the stored edge `j`, from `x_j` to `x_{j+1}`. The holonomy of the path
`γ = x₀ → ⋯ → x_R` is `P = Hol_U(γ) = U_R ⋯ U_1` (`eq:path-holonomy`, `Skeleton.hol`).

* **Matter at the two ends.** A gauge change `h = (h_{x_j})` moves the links by
  `U ↦ h_{x_{j+1}} U h_{x_j}⁻¹` (`Skeleton.gaugeAct`) and the matter at the two ends by a matrix
  `Γ(h_{x₀}, h_{x_R})` (a representation `Γ` of the gauge pair, as for one edge). A state is a
  coefficient table over the link tables with values in the coefficient tables of the matter,
  and it is colourless when `ψ(U^h) = Γ(h_{x₀}, h_{x_R}) ψ(U)` for all `h` and `U`
  (`PathCanvas.colourless`). The one-edge condition of Definition 11.13 with this matter is
  `Edge.colourlessWith`.
* **Static sources.** A quark source is one triplet index moved by `ρ(h)`, an antiquark source
  one index moved by the conjugate `conj ρ(h)` (`Edge.conjTriplet`). The matter of the string
  model at its two ends is a source at each end and the occupation tables of `d = |S|` slots at
  each end, the modes of one edge (`PathCanvas.endMatter`); with no dynamical quarks it is the two
  sources alone (`PathCanvas.sourcePair`).
* **The string** is `ψ_{cc'}(U) = (U_1⁻¹ ⋯ U_R⁻¹)_{cc'} = ρ(P⁻¹)_{cc'}` (`PathCanvas.string`, and
  `PathCanvas.stringState` with empty occupation tables).
* **Energies.** An operator on the tables of one link acts on the table of the link `e` of a
  state, the other links fixed (`Canvas.onLink`); the electric energy of the string law is the sum
  over the links (`PathCanvas.electric`), and the declared mass term counts the dynamical quarks
  (`PathCanvas.mass`).
-/

namespace Artform

open scoped Matrix ComplexConjugate

namespace Canvas

variable (K : Canvas) {G : Type*} [Group G]

/-- The link table `U` with the value `g` on the stored edge `e`, and `g⁻¹` on its reversal; the
other links keep their values. -/
def setLink (U : K.skeleton.LinkTable G) (e : K.E) (g : G) : K.skeleton.LinkTable G :=
  Skeleton.LinkTable.ofGraph (Function.update (fun e' => U (e', true)) e g)

/-- An operator `X` on the coefficient tables of one link, acting on the table of the link `e` of
a state `ψ` of the canvas: with the other links fixed, `ψ` is a table over the value `g` of `e`,
and `(X_e ψ)(U) = (X (g ↦ ψ(U with g on e)))(U_e)`. -/
def onLink {A : Type*} (X : (G → A) → (G → A)) (e : K.E) (ψ : K.skeleton.LinkTable G → A) :
    K.skeleton.LinkTable G → A :=
  fun U => X (fun g => ψ (K.setLink U e g)) (U (e, true))

/-- The path `Path(R) = (x₀ → x₁ → ⋯ → x_R)` as a canvas (Section 13.1): the vertices `x_j`,
`j = 0, …, R`, the stored edge `j` from `x_j` to `x_{j+1}`, and no faces. -/
abbrev path (R : ℕ) : Canvas where
  V := Fin (R + 1)
  E := Fin R
  F := Empty
  src j := j.castSucc
  tgt j := j.succ
  boundary f := f.elim
  closed f := f.elim

end Canvas

/-- An operator on complex-valued tables, applied component by component to tables with values
in `N → ℂ`. -/
def liftTable {G N : Type*} (X : (G → ℂ) → (G → ℂ)) (f : G → N → ℂ) : G → N → ℂ :=
  fun g x => X (fun g' => f g' x) g

namespace Edge

variable {G : Type*} [Group G] {C : Type*} [Fintype C] [DecidableEq C]

/-- The conjugate triplet `g ↦ conj ρ(g)`, which moves an antiquark source. -/
noncomputable def conjTriplet (ρ : G →* Matrix C C ℂ) : G →* Matrix C C ℂ :=
  (RingHom.mapMatrix (starRingEnd ℂ)).toMonoidHom.comp ρ

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The colourless states of one edge `x → y` whose matter, at its two ends, moves by
`Γ(h_x, h_y)` under the gauge pair: `φ(h_y P h_x⁻¹) = Γ(h_x, h_y) φ(P)` for all `h_x`, `h_y`
and link values `P`. With the occupation tables of the two ends as the matter this is
Definition 11.13 (`Edge.colourless`). -/
def colourlessWith (Γ : G × G →* Matrix N N ℂ) : Submodule ℂ (G → N → ℂ) where
  carrier := {φ | ∀ hx hy P, φ (hy * P * hx⁻¹) = Γ (hx, hy) *ᵥ φ P}
  add_mem' {φ φ'} hφ hφ' hx hy P := by
    simp only [Set.mem_ofPred_eq] at hφ hφ'
    simp only [Pi.add_apply, hφ, hφ', Matrix.mulVec_add]
  zero_mem' hx hy P := by simp
  smul_mem' c φ hφ hx hy P := by
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [Pi.smul_apply, hφ, Matrix.mulVec_smul]

end Edge

namespace PathCanvas

variable (R : ℕ)

/-- The first vertex `x₀` of the path. -/
def x0 : (Canvas.path R).V := ⟨0, Nat.succ_pos R⟩

/-- The last vertex `x_R` of the path. -/
def xR : (Canvas.path R).V := Fin.last R

/-- The path `x₀ → x₁ → ⋯ → x_j` along the stored edges. -/
def pathTo : (j : ℕ) → (hj : j < R + 1) → (Canvas.path R).skeleton.Path (x0 R) ⟨j, hj⟩
  | 0, _ => .nil _
  | j + 1, hj => @Skeleton.Path.cons (Canvas.path R).skeleton (x0 R)
      ((⟨j, by omega⟩ : Fin R), true) (pathTo j (by omega))

/-- The path `γ = x₀ → x₁ → ⋯ → x_R`, whose holonomy is `P = U_R ⋯ U_1`. -/
def γ : (Canvas.path R).skeleton.Path (x0 R) (xR R) := pathTo R R (Nat.lt_succ_self R)

variable {G : Type*} [Group G] {N : Type*} [Fintype N] [DecidableEq N]

/-- The colourless states of a path whose matter sits at its two ends and moves by
`Γ(h_{x₀}, h_{x_R})`: the coefficient tables `ψ` over the link tables with
`ψ(U^h) = Γ(h_{x₀}, h_{x_R}) ψ(U)` for every gauge change `h` and every `U`. -/
def colourless (Γ : G × G →* Matrix N N ℂ) :
    Submodule ℂ ((Canvas.path R).skeleton.LinkTable G → N → ℂ) where
  carrier := {ψ | ∀ (h : (Canvas.path R).V → G) U,
    ψ (Skeleton.gaugeAct h U) = Γ (h (x0 R), h (xR R)) *ᵥ ψ U}
  add_mem' {ψ φ} hψ hφ h U := by
    simp only [Set.mem_ofPred_eq] at hψ hφ
    simp only [Pi.add_apply, hψ, hφ, Matrix.mulVec_add]
  zero_mem' h U := by simp
  smul_mem' c ψ hψ h U := by
    simp only [Set.mem_ofPred_eq] at hψ
    simp only [Pi.smul_apply, hψ, Matrix.mulVec_smul]

/-- The zero-flux states of the path: colourless, and constant in the link table, so that every
link's table lies in the trivial block and each end is colourless on its own. -/
def zeroFlux (Γ : G × G →* Matrix N N ℂ) :
    Submodule ℂ ((Canvas.path R).skeleton.LinkTable G → N → ℂ) where
  carrier := {ψ | ψ ∈ colourless R Γ ∧ ∀ U V, ψ U = ψ V}
  add_mem' {ψ φ} hψ hφ := ⟨(colourless R Γ).add_mem hψ.1 hφ.1, fun U V => by
    simp only [Pi.add_apply, hψ.2 U V, hφ.2 U V]⟩
  zero_mem' := ⟨(colourless R Γ).zero_mem, fun _ _ => rfl⟩
  smul_mem' c ψ hψ := ⟨(colourless R Γ).smul_mem c hψ.1, fun U V => by
    simp only [Pi.smul_apply, hψ.2 U V]⟩

variable {C : Type*} [Fintype C] [DecidableEq C] {S : Type*} [Fintype S] [DecidableEq S]

/-- The two static sources alone: a source at `x₀` moved by `σ₀` and one at `x_R` moved by
`σ_R`, on the pairs `(c, c')` of their indices: `(h_{x₀}, h_{x_R}) ↦ σ₀(h_{x₀}) ⊗ σ_R(h_{x_R})`. -/
noncomputable def sourcePair (σ₀ σR : G →* Matrix C C ℂ) : G × G →* Matrix (C × C) (C × C) ℂ where
  toFun h := Matrix.kroneckerMap (· * ·) (σ₀ h.1) (σR h.2)
  map_one' := by simp
  map_mul' h k := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    exact Matrix.mul_kronecker_mul _ _ _ _

/-- The matter at the two ends of the string model: a static source at `x₀` moved by `σ₀`, one at
`x_R` moved by `σ_R`, and the occupation tables of `d = |S|` slots at each end, the modes of one
edge from `x₀` to `x_R` (`Edge.Mode`), moved by `Γ_x(h_{x₀}) Γ_y(h_{x_R})` (Section 11.5), in
the chosen order `ord` of the modes. -/
noncomputable def endMatter (σ₀ σR ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Edge.Mode C S)) :
    G × G →* Matrix ((C × C) × Finset (Edge.Mode C S)) ((C × C) × Finset (Edge.Mode C S)) ℂ where
  toFun h := Matrix.kroneckerMap (· * ·) (sourcePair σ₀ σR h) (Edge.pairHom ρ ord h)
  map_one' := by simp
  map_mul' h k := by
    simp only [map_mul]
    exact Matrix.mul_kronecker_mul _ _ _ _

/-- The states of the string model whose every coefficient table has `k` dynamical quarks. -/
def quarkSector (k : ℕ) :
    Submodule ℂ ((Canvas.path R).skeleton.LinkTable G → (C × C) × Finset (Edge.Mode C S) → ℂ) where
  carrier := {ψ | ∀ U x, ψ U x ≠ 0 → x.2.card = k}
  add_mem' {ψ φ} hψ hφ U x hx := by
    by_cases h : ψ U x = 0
    · exact hφ U x (by simpa [h] using hx)
    · exact hψ U x h
  zero_mem' U x hx := absurd rfl hx
  smul_mem' c ψ hψ U x hx := hψ U x (right_ne_zero_of_mul hx)

/-- The states of the string model whose every coefficient table has `k₀` dynamical quarks at
`x₀` and `k_R` at `x_R`. -/
def endSector (k₀ kR : ℕ) :
    Submodule ℂ ((Canvas.path R).skeleton.LinkTable G → (C × C) × Finset (Edge.Mode C S) → ℂ) where
  carrier := {ψ | ∀ U x, ψ U x ≠ 0 → x.2.toLeft.card = k₀ ∧ x.2.toRight.card = kR}
  add_mem' {ψ φ} hψ hφ U x hx := by
    by_cases h : ψ U x = 0
    · exact hφ U x (by simpa [h] using hx)
    · exact hψ U x h
  zero_mem' U x hx := absurd rfl hx
  smul_mem' c ψ hψ U x hx := hψ U x (right_ne_zero_of_mul hx)

/-- **The string**, `ψ_{cc'}(U_1, …, U_R) = (U_1⁻¹ U_2⁻¹ ⋯ U_R⁻¹)_{cc'} = ρ(P⁻¹)_{cc'}` with
`P = Hol_U(γ) = U_R ⋯ U_1`, `c` the index of the source at `x₀` and `c'` that at `x_R`: the
antiquark's colour transported back along the path to the quark. -/
noncomputable def string (ρ : G →* Matrix C C ℂ) :
    (Canvas.path R).skeleton.LinkTable G → C × C → ℂ :=
  fun U x => ρ (Skeleton.hol U (γ R))⁻¹ x.1 x.2

/-- The string as a state of the string model with slots at the ends: the string on the source
indices, and the empty occupation table at both ends. -/
noncomputable def stringState (ρ : G →* Matrix C C ℂ) :
    (Canvas.path R).skeleton.LinkTable G → (C × C) × Finset (Edge.Mode C S) → ℂ :=
  fun U x => if x.2 = ∅ then string R ρ U x.1 else 0

/-- The electric energy of the string law, `Σ_{j=1}^R H_{E,j}`, for an operator `X` on the
complex tables of one link: `X` acts on the table of each link in turn, component by
component. -/
def electric (X : (G → ℂ) → (G → ℂ))
    (ψ : (Canvas.path R).skeleton.LinkTable G → N → ℂ) :
    (Canvas.path R).skeleton.LinkTable G → N → ℂ :=
  ∑ j : Fin R, (Canvas.path R).onLink (liftTable X) j ψ

/-- The declared mass term `H_M = M Σ_m n_m`: it multiplies a coefficient by `M` times the number
of dynamical quarks of its occupation table. -/
def mass (M : ℝ)
    (ψ : (Canvas.path R).skeleton.LinkTable G → (C × C) × Finset (Edge.Mode C S) → ℂ) :
    (Canvas.path R).skeleton.LinkTable G → (C × C) × Finset (Edge.Mode C S) → ℂ :=
  fun U x => ((M : ℂ) * x.2.card) * ψ U x

/-- A state that is constant in the link table, with the value `v`. -/
def constState (v : N → ℂ) : (Canvas.path R).skeleton.LinkTable G → N → ℂ := fun _ => v

/-- **One quark at each source.** The vector
`Σ_{c,c'} |c, c'⟩ ⊗ a†_{x₀ c s} a†_{x_R c' t} |0⟩` of the matter at the ends: a quark in the
slot `s` at the quark source, its colour paired with the source's, and a quark in the slot `t` at
the antiquark source, its colour paired with that source's. -/
noncomputable def pairScreen (ord : LinearOrder (Edge.Mode (Fin 3) S)) (s t : S) :
    (Fin 3 × Fin 3) × Finset (Edge.Mode (Fin 3) S) → ℂ :=
  fun x => ((Fock.creation ord (Sum.inl (x.1.1, s)) * Fock.creation ord (Sum.inr (x.1.2, t))) *ᵥ
    Fock.ket ∅) x.2

/-- **The antisymmetric colour pair at the quark source.** The vector
`Σ_{c,a,b,c'} ε_{cab} |c, c'⟩ ⊗ a†_{x₀ a s} a†_{x₀ b t} a†_{x_R c' u} |0⟩`: two quarks at the
quark source, in the slots `s` and `t`, in the antisymmetric colour pair against the source, and
a quark in the slot `u` at the antiquark source, its colour paired with that source's. -/
noncomputable def baryonScreen (ord : LinearOrder (Edge.Mode (Fin 3) S)) (s t u : S) :
    (Fin 3 × Fin 3) × Finset (Edge.Mode (Fin 3) S) → ℂ :=
  fun x => ((∑ a, ∑ b, leviCivita x.1.1 a b • (Fock.creation ord (Sum.inl (a, s)) *
    Fock.creation ord (Sum.inl (b, t)) * Fock.creation ord (Sum.inr (x.1.2, u)))) *ᵥ
    Fock.ket ∅) x.2

end PathCanvas

/-- The invariants of `3 ⊗ 3`: the tensors `T`, written as matrices, with `ρ(g) T ρ(g)ᵀ = T` for
every `g`. Their number is `⟨χ²⟩` (`fig:mm-moments`). -/
def pairInvariants {G : Type*} [Group G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) :
    Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ) where
  carrier := {T | ∀ g, ρ g * T * (ρ g)ᵀ = T}
  add_mem' {T T'} hT hT' g := by
    simp only [Set.mem_ofPred_eq] at hT hT'
    rw [Matrix.mul_add, Matrix.add_mul, hT, hT']
  zero_mem' g := by simp
  smul_mem' c T hT g := by
    simp only [Set.mem_ofPred_eq] at hT
    rw [Matrix.mul_smul, Matrix.smul_mul, hT]

namespace ColourGroups

/-- The triplet of a colour group `G ≤ SU(3)`: its inclusion into the `3 × 3` matrices. -/
def subTriplet (H : Subgroup (Matrix.specialUnitaryGroup (Fin 3) ℂ)) :
    H →* Matrix (Fin 3) (Fin 3) ℂ :=
  (Matrix.specialUnitaryGroup (Fin 3) ℂ).subtype.comp H.subtype

/-- The triplet of `C₃ × A₅` (Definition 12.11), `(ω^j, g) ↦ ω^j g`, as matrices. -/
noncomputable def c3a5Triplet : C3A5 →* Matrix (Fin 3) (Fin 3) ℂ :=
  (Matrix.specialUnitaryGroup (Fin 3) ℂ).subtype.comp C3A5.triplet

/-- The triplet of `SU(3)`: its inclusion into the `3 × 3` matrices. -/
def su3Triplet : Matrix.specialUnitaryGroup (Fin 3) ℂ →* Matrix (Fin 3) (Fin 3) ℂ :=
  (Matrix.specialUnitaryGroup (Fin 3) ℂ).subtype

end ColourGroups

end Artform
