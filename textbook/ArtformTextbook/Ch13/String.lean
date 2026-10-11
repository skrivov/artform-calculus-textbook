import ArtformTextbook.Ch11.ThereAndBack
import ArtformTextbook.Ch11.Averaging
import ArtformTextbook.Ch13.Statements.String

/-!
# A flux string (Propositions 13.1, 13.3, 13.4, Theorem 13.2)

* **Absorption.** On the path, the gauge change `h_{x_j} = (U_j ⋯ U_1)⁻¹` for `j < R` and
  `h_{x_R} = 1` carries every link table to the table `std(P)` with `P = U_R ⋯ U_1` on the last
  link and `1` on the others (`PathCanvas.gaugeAct_toStd`); it is `1` at both ends, so a
  colourless state takes the same value at `U` and at `std(P)` (`PathCanvas.eq_std`). The gauge
  change `h_x` at every vertex but the last and `h_y` at the last carries `std(P)` to
  `std(h_y P h_x⁻¹)`, so `P ↦ ψ(std P)` is a colourless state of one edge, and `ψ ↦ (P ↦ ψ(std P))`
  is a linear isomorphism whose inverse is `φ ↦ φ ∘ P` (`PathCanvas.edgeEquiv`).
* **Gauge fixing on the edge.** A colourless state of one edge is determined by `φ(1)`, which is
  any vector fixed by the diagonal `Γ(h, h)` (`Edge.colourlessWithEquiv`), as in
  Proposition 11.14; so the count is the average of the trace of `Γ(h, h)` (Proposition 11.5).
  For the sources and the slots of the string model that trace is
  `χ(h) conj(χ(h)) det(1 + z ρ(h))^{2d}` at `z^k`.
* **The string (Theorem 13.2).** With the sources alone a colourless state is `ψ(std P) = M` with
  `ρ(g) M conj(ρ(g'))ᵀ = M`; the half-turns `H_0`, `H_1`, `H_2` and the third-turn `T_3`, which lie
  in each of the five groups, make `M` scalar (`StringLine.commutant`), so the string spans. With
  two quark sources `ρ(g) M ρ(g)ᵀ = M` forces `M = 0` when `ω 1` is in the group and `M` scalar
  when the triplet is real. The string's table on each link is a matrix coefficient of the
  conjugate triplet, so the declared energy multiplies it by `E₃` on every link.
* **Screening (Proposition 13.3).** A zero-flux state is a constant table whose value is an end
  vector fixed by every gauge pair (`PathCanvas.zeroFlux_inf_eq`), so by Proposition 11.5 those
  with `k` quarks number the coefficient of `z^k` in `⟨χ P⟩ ⟨χ̄ P⟩` with `P = det(1 + z g)²`
  (`StringLine.screen_count`): none with `0` or `1` quark, `4⟨χ²⟩` with two, and `2(⟨χ³⟩ + 2)`
  with three when `⟨χ²⟩ = 0`. The moments `⟨χ⟩ = 0`, `⟨χ χ̄⟩ = 1`, `⟨χ²⟩` and `⟨χ³⟩ = 1` of the four
  finite groups are exact sums, and `SU(3)` fixes no more vectors than its subgroup `C₃ × A₅`. The
  named states are fixed (`ε_{abc} g_{ia} g_{jb} g_{kc} = det g ε_{ijk}` for the antisymmetric
  pair) and independent, so they span.
* **Levels (Proposition 13.4).** The string has no quark and lies in the conjugate triplet block on
  every link; a zero-flux state is constant in the links, so each link's table is constant and the
  declared energy kills it, and its `k_min` quarks give the mass `k_min M`. The hop moves one quark,
  so it keeps their number.
-/

namespace Artform

open scoped Matrix ComplexConjugate

open Polynomial

namespace PathCanvas

variable {G : Type*} [Group G]

/-! ### The path and its holonomies -/

/-- Two link tables of the path that agree on every stored edge are equal. -/
theorem linkTable_ext {R : ℕ} {U V : (Canvas.path R).skeleton.LinkTable G}
    (h : ∀ j : Fin R, U (j, true) = V (j, true)) : U = V := by
  ext ⟨j, b⟩
  cases b
  · rw [show U (j, false) = (U (j, true))⁻¹ from U.reversal (j, true),
      show V (j, false) = (V (j, true))⁻¹ from V.reversal (j, true), h j]
  · exact h j

theorem hol_pathTo_zero (R : ℕ) (U : (Canvas.path R).skeleton.LinkTable G) (h : 0 < R + 1) :
    Skeleton.hol U (pathTo R 0 h) = 1 := rfl

theorem hol_pathTo_succ (R : ℕ) (U : (Canvas.path R).skeleton.LinkTable G) (j : ℕ)
    (h : j + 1 < R + 1) :
    Skeleton.hol U (pathTo R (j + 1) h) =
      U ((⟨j, by omega⟩ : Fin R), true) * Skeleton.hol U (pathTo R j (by omega)) := rfl

/-- The link table with `g` on the last link `U_R` and `1` on the others. -/
def std (R : ℕ) (g : G) : (Canvas.path R).skeleton.LinkTable G :=
  Skeleton.LinkTable.ofGraph fun j : Fin R => if (j : ℕ) + 1 = R then g else 1

theorem std_apply (R : ℕ) (g : G) (j : Fin R) :
    std R g (j, true) = if (j : ℕ) + 1 = R then g else 1 := rfl

theorem hol_std_pathTo (R : ℕ) (hR : 0 < R) (g : G) :
    ∀ (j : ℕ) (hj : j < R + 1), Skeleton.hol (std R g) (pathTo R j hj) = if j = R then g else 1
  | 0, hj => by
    rw [hol_pathTo_zero, ite_eq_right (by omega)]
  | j + 1, hj => by
    rw [hol_pathTo_succ, hol_std_pathTo R hR g j (by omega), ite_eq_right (by omega),
      mul_one, std_apply]

/-- The holonomy of `std(g)` is `g`. -/
theorem hol_std (R : ℕ) (hR : 0 < R) (g : G) : Skeleton.hol (std R g) (γ R) = g :=
  (hol_std_pathTo R hR g R (Nat.lt_succ_self R)).trans (ite_eq_left rfl)

/-- The gauge change that carries `U` to `std(U_R ⋯ U_1)`: `(U_j ⋯ U_1)⁻¹` at `x_j` for `j < R`,
and `1` at `x_R`. -/
def toStd (R : ℕ) (U : (Canvas.path R).skeleton.LinkTable G) : (Canvas.path R).V → G :=
  fun v : Fin (R + 1) => if h : (v : ℕ) < R then (Skeleton.hol U (pathTo R v (by omega)))⁻¹ else 1

theorem toStd_of_lt (R : ℕ) (U : (Canvas.path R).skeleton.LinkTable G) (v : Fin (R + 1))
    (h : (v : ℕ) < R) : toStd R U v = (Skeleton.hol U (pathTo R v (by omega)))⁻¹ := by
  unfold toStd
  rw [dite_eq_left h]

theorem toStd_of_not_lt (R : ℕ) (U : (Canvas.path R).skeleton.LinkTable G) (v : Fin (R + 1))
    (h : ¬ (v : ℕ) < R) : toStd R U v = 1 := by
  unfold toStd
  rw [dite_eq_right h]

theorem toStd_x0 (R : ℕ) (hR : 0 < R) (U : (Canvas.path R).skeleton.LinkTable G) :
    toStd R U (x0 R) = 1 := by
  rw [toStd_of_lt R U (x0 R) hR]
  exact inv_one

theorem toStd_xR (R : ℕ) (U : (Canvas.path R).skeleton.LinkTable G) : toStd R U (xR R) = 1 :=
  toStd_of_not_lt R U (xR R) (by simp [xR])

/-- `U^{toStd(U)} = std(U_R ⋯ U_1)`. -/
theorem gaugeAct_toStd (R : ℕ) (U : (Canvas.path R).skeleton.LinkTable G) :
    Skeleton.gaugeAct (toStd R U) U = std R (Skeleton.hol U (γ R)) := by
  apply linkTable_ext
  rintro ⟨j, hj⟩
  rw [Skeleton.gaugeAct_apply, std_apply]
  change toStd R U ⟨j + 1, by omega⟩ * U (⟨j, hj⟩, true) * (toStd R U ⟨j, by omega⟩)⁻¹ = _
  rw [toStd_of_lt R U ⟨j, by omega⟩ hj, inv_inv]
  by_cases hjR : j + 1 = R
  · rw [toStd_of_not_lt R U ⟨j + 1, by omega⟩ (by change ¬ j + 1 < R; omega), one_mul]
    change _ = if j + 1 = R then _ else _
    rw [ite_eq_left hjR]
    subst hjR
    exact (hol_pathTo_succ (j + 1) U j (by omega)).symm
  · rw [toStd_of_lt R U ⟨j + 1, by omega⟩ (by change j + 1 < R; omega)]
    change _ = if j + 1 = R then _ else _
    rw [ite_eq_right hjR, hol_pathTo_succ]
    group

/-- The gauge change `h_x` at `x₀, …, x_{R-1}` and `h_y` at `x_R`. -/
def endChange (R : ℕ) (hx hy : G) : (Canvas.path R).V → G :=
  fun v : Fin (R + 1) => if (v : ℕ) = R then hy else hx

omit [Group G] in
theorem endChange_of_eq (R : ℕ) (hx hy : G) (v : Fin (R + 1)) (h : (v : ℕ) = R) :
    endChange R hx hy v = hy := by
  unfold endChange
  rw [ite_eq_left h]

omit [Group G] in
theorem endChange_of_ne (R : ℕ) (hx hy : G) (v : Fin (R + 1)) (h : (v : ℕ) ≠ R) :
    endChange R hx hy v = hx := by
  unfold endChange
  rw [ite_eq_right h]

/-- `std(P)^{endChange} = std(h_y P h_x⁻¹)`. -/
theorem gaugeAct_endChange (R : ℕ) (hx hy P : G) :
    Skeleton.gaugeAct (endChange R hx hy) (std R P) = std R (hy * P * hx⁻¹) := by
  apply linkTable_ext
  rintro ⟨j, hj⟩
  rw [Skeleton.gaugeAct_apply]
  change endChange R hx hy ⟨j + 1, by omega⟩ * std R P (⟨j, hj⟩, true) *
    (endChange R hx hy ⟨j, by omega⟩)⁻¹ = std R (hy * P * hx⁻¹) (⟨j, hj⟩, true)
  rw [std_apply, std_apply, endChange_of_ne R hx hy ⟨j, by omega⟩ (by change j ≠ R; omega)]
  by_cases hjR : j + 1 = R
  · rw [endChange_of_eq R hx hy ⟨j + 1, by omega⟩ hjR]
    simp only [hjR, ite_true]
  · rw [endChange_of_ne R hx hy ⟨j + 1, by omega⟩ hjR]
    simp only [hjR, ite_false]
    group

omit [Group G] in
theorem endChange_x0 (R : ℕ) (hR : 0 < R) (hx hy : G) : endChange R hx hy (x0 R) = hx :=
  endChange_of_ne R hx hy (x0 R) (by change 0 ≠ R; omega)

omit [Group G] in
theorem endChange_xR (R : ℕ) (hx hy : G) : endChange R hx hy (xR R) = hy :=
  endChange_of_eq R hx hy (xR R) rfl

/-! ### Absorption -/

variable {N : Type*} [Fintype N] [DecidableEq N] {R : ℕ}

/-- A colourless state takes the same value at `U` and at `std(U_R ⋯ U_1)`. -/
theorem eq_std (hR : 0 < R) {Γ : G × G →* Matrix N N ℂ} {ψ} (hψ : ψ ∈ colourless R Γ)
    (U : (Canvas.path R).skeleton.LinkTable G) : ψ U = ψ (std R (Skeleton.hol U (γ R))) := by
  rw [← gaugeAct_toStd, hψ (toStd R U) U, toStd_x0 R hR, toStd_xR,
    show ((1 : G), (1 : G)) = 1 from rfl, map_one, Matrix.one_mulVec]

/-- The colourless state of one edge read off a colourless state of the path:
`P ↦ ψ(std P)`. -/
def toEdge (ψ : (Canvas.path R).skeleton.LinkTable G → N → ℂ) : G → N → ℂ :=
  fun P => ψ (std R P)

theorem toEdge_mem (hR : 0 < R) {Γ : G × G →* Matrix N N ℂ} {ψ} (hψ : ψ ∈ colourless R Γ) :
    toEdge ψ ∈ Edge.colourlessWith Γ := by
  intro hx hy P
  change ψ (std R (hy * P * hx⁻¹)) = Γ (hx, hy) *ᵥ ψ (std R P)
  rw [← gaugeAct_endChange, hψ, endChange_x0 R hR, endChange_xR]

theorem ofEdge_mem {Γ : G × G →* Matrix N N ℂ} {φ : G → N → ℂ}
    (hφ : φ ∈ Edge.colourlessWith Γ) :
    (fun U : (Canvas.path R).skeleton.LinkTable G => φ (Skeleton.hol U (γ R))) ∈
      colourless R Γ := by
  intro h U
  change φ (Skeleton.hol (Skeleton.gaugeAct h U) (γ R)) = _
  rw [Skeleton.hol_gaugeAct]
  exact hφ _ _ _

/-- The colourless states of the path are the colourless states of one edge with link `P`. -/
def edgeEquiv (hR : 0 < R) (Γ : G × G →* Matrix N N ℂ) :
    ↥(colourless R Γ) ≃ₗ[ℂ] ↥(Edge.colourlessWith Γ) where
  toFun ψ := ⟨toEdge ψ.1, toEdge_mem hR ψ.2⟩
  invFun φ := ⟨fun U => φ.1 (Skeleton.hol U (γ R)), ofEdge_mem φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv ψ := Subtype.ext (funext fun U => (eq_std hR ψ.2 U).symm)
  right_inv φ := Subtype.ext (funext fun P => by
    change φ.1 (Skeleton.hol (std R P) (γ R)) = φ.1 P
    rw [hol_std R hR])

theorem edgeEquiv_apply (hR : 0 < R) (Γ : G × G →* Matrix N N ℂ) (ψ : ↥(colourless R Γ))
    (U : (Canvas.path R).skeleton.LinkTable G) :
    (edgeEquiv hR Γ ψ : G → N → ℂ) (Skeleton.hol U (γ R)) = ψ.1 U :=
  (eq_std hR ψ.2 U).symm

end PathCanvas

/-! ### Gauge fixing on one edge -/

namespace Edge

variable {G : Type*} [Group G] {N : Type*} [Fintype N] [DecidableEq N]

/-- The diagonal gauge pairs, `h ↦ Γ(h, h)`. -/
def diagGauge (Γ : G × G →* Matrix N N ℂ) : G →* Matrix N N ℂ :=
  Γ.comp ((MonoidHom.id G).prod (MonoidHom.id G))

theorem diagGauge_apply (Γ : G × G →* Matrix N N ℂ) (h : G) : diagGauge Γ h = Γ (h, h) := rfl

/-- Gauge fixing: a state is colourless exactly when `φ(P) = Γ(1, P) φ(1)` for every `P` and
`φ(1)` is fixed by the diagonal pairs. -/
theorem mem_colourlessWith_iff (Γ : G × G →* Matrix N N ℂ) (φ : G → N → ℂ) :
    φ ∈ colourlessWith Γ ↔ (∀ P, φ P = Γ (1, P) *ᵥ φ 1) ∧ ∀ h, Γ (h, h) *ᵥ φ 1 = φ 1 := by
  constructor
  · intro hφ
    refine ⟨fun P => ?_, fun h => ?_⟩
    · have := hφ 1 P 1
      rwa [mul_one, inv_one, mul_one] at this
    · have := hφ h h 1
      rw [mul_one, mul_inv_cancel] at this
      exact this.symm
  · rintro ⟨hP, hd⟩ hx hy P
    rw [hP (hy * P * hx⁻¹), hP P, Matrix.mulVec_mulVec]
    conv_rhs => rw [← hd hx⁻¹, Matrix.mulVec_mulVec]
    rw [← map_mul, ← map_mul]
    congr 2
    ext <;> simp

/-- `φ ↦ φ(1)` is a linear isomorphism of the colourless states whose values lie in a subspace
`Z` that every `Γ(1, P)` keeps onto the vectors of `Z` fixed by the diagonal pairs. -/
def colourlessWithEquiv (Γ : G × G →* Matrix N N ℂ) (Z : Submodule ℂ (N → ℂ))
    (hZ : ∀ (P : G) (v : N → ℂ), v ∈ Z → Γ (1, P) *ᵥ v ∈ Z) :
    ↥(colourlessWith Γ ⊓ Submodule.pi Set.univ (fun _ : G => Z)) ≃ₗ[ℂ]
      ↥(Z ⊓ Fock.fixedSub (diagGauge Γ)) where
  toFun φ := ⟨φ.1 1, (Submodule.mem_pi.mp (Submodule.mem_inf.mp φ.2).2) 1 (Set.mem_univ _),
    fun h => ((mem_colourlessWith_iff Γ φ.1).mp (Submodule.mem_inf.mp φ.2).1).2 h⟩
  invFun v := ⟨fun P => Γ (1, P) *ᵥ v.1,
    (mem_colourlessWith_iff Γ _).mpr ⟨fun P => by
        rw [show ((1 : G), (1 : G)) = 1 from rfl, map_one, Matrix.one_mulVec],
      fun h => by
        rw [show ((1 : G), (1 : G)) = 1 from rfl, map_one, Matrix.one_mulVec]
        exact (Submodule.mem_inf.mp v.2).2 h⟩,
    Submodule.mem_pi.mpr fun P _ => hZ P _ (Submodule.mem_inf.mp v.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext (funext fun P =>
    (((mem_colourlessWith_iff Γ φ.1).mp (Submodule.mem_inf.mp φ.2).1).1 P).symm)
  right_inv v := Subtype.ext (by
    change Γ (1, 1) *ᵥ v.1 = v.1
    rw [show ((1 : G), (1 : G)) = 1 from rfl, map_one, Matrix.one_mulVec])

end Edge

namespace PathCanvas

variable {G : Type*} [Group G] {N : Type*} [Fintype N] [DecidableEq N] {R : ℕ}

/-- The isomorphism of Proposition 13.1, restricted to the states whose values lie in `Z`. -/
def edgeEquivSector (hR : 0 < R) (Γ : G × G →* Matrix N N ℂ) (Z : Submodule ℂ (N → ℂ)) :
    ↥(colourless R Γ ⊓ Submodule.pi Set.univ
        (fun _ : (Canvas.path R).skeleton.LinkTable G => Z)) ≃ₗ[ℂ]
      ↥(Edge.colourlessWith Γ ⊓ Submodule.pi Set.univ (fun _ : G => Z)) where
  toFun ψ := ⟨toEdge ψ.1, toEdge_mem hR (Submodule.mem_inf.mp ψ.2).1,
    Submodule.mem_pi.mpr fun P _ =>
      (Submodule.mem_pi.mp (Submodule.mem_inf.mp ψ.2).2) _ (Set.mem_univ _)⟩
  invFun φ := ⟨fun U => φ.1 (Skeleton.hol U (γ R)), ofEdge_mem (Submodule.mem_inf.mp φ.2).1,
    Submodule.mem_pi.mpr fun U _ =>
      (Submodule.mem_pi.mp (Submodule.mem_inf.mp φ.2).2) _ (Set.mem_univ _)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv ψ := Subtype.ext (funext fun U => (eq_std hR (Submodule.mem_inf.mp ψ.2).1 U).symm)
  right_inv φ := Subtype.ext (funext fun P => by
    change φ.1 (Skeleton.hol (std R P) (γ R)) = φ.1 P
    rw [hol_std R hR])

/-- **Counting.** The colourless states of the path with values in the tables supported on `p`
number `(1/|G|) Σ_h Σ_{n ∈ p} Γ(h, h)_{nn}`. -/
theorem finrank_colourless_sector [Fintype G] (hR : 0 < R) (Γ : G × G →* Matrix N N ℂ)
    (p : N → Prop) [DecidablePred p] (hp : ∀ h n' n, Γ h n' n ≠ 0 → (p n' ↔ p n)) :
    (Module.finrank ℂ ↥(colourless R Γ ⊓ Submodule.pi Set.univ
        (fun _ : (Canvas.path R).skeleton.LinkTable G =>
          ({ carrier := {v | ∀ n, v n ≠ 0 → p n}
             add_mem' := fun {v w} hv hw n hn => by
               by_cases h : v n = 0
               · exact hw n (by simpa [h] using hn)
               · exact hv n h
             zero_mem' := fun n hn => absurd rfl hn
             smul_mem' := fun c v hv n hn => hv n (right_ne_zero_of_mul hn) } :
            Submodule ℂ (N → ℂ)))) : ℂ) =
      (Fintype.card G : ℂ)⁻¹ * ∑ h, ∑ n ∈ Finset.univ.filter p, Γ (h, h) n n := by
  set Z : Submodule ℂ (N → ℂ) :=
    { carrier := {v | ∀ n, v n ≠ 0 → p n}
      add_mem' := fun {v w} hv hw n hn => by
        by_cases h : v n = 0
        · exact hw n (by simpa [h] using hn)
        · exact hv n h
      zero_mem' := fun n hn => absurd rfl hn
      smul_mem' := fun c v hv n hn => hv n (right_ne_zero_of_mul hn) } with hZdef
  have hZ : ∀ (P : G) (v : N → ℂ), v ∈ Z → Γ (1, P) *ᵥ v ∈ Z := fun P v hv =>
    Fock.mulVec_mem_of_respects (Γ (1, P)) p (hp (1, P)) hv
  rw [LinearEquiv.finrank_eq ((edgeEquivSector hR Γ Z).trans (Edge.colourlessWithEquiv Γ Z hZ)),
    Fock.finrank_inf_fixedSub (Edge.diagGauge Γ) p Z (fun v => Iff.rfl) (fun h => hp (h, h))]
  rfl

section Count

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

theorem endMatter_apply (σ₀ σR ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Edge.Mode C S))
    (h : G × G) (y y' : (C × C) × Finset (Edge.Mode C S)) :
    endMatter σ₀ σR ρ ord h y y' =
      σ₀ h.1 y.1.1 y'.1.1 * σR h.2 y.1.2 y'.1.2 * Edge.pairHom ρ ord h y.2 y'.2 := rfl

/-- The matter of the string model keeps the number of dynamical quarks. -/
theorem endMatter_respects (σ₀ σR ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Edge.Mode C S))
    (k : ℕ) (h : G × G) (y y' : (C × C) × Finset (Edge.Mode C S))
    (hne : endMatter σ₀ σR ρ ord h y y' ≠ 0) : (y.2.card = k ↔ y'.2.card = k) := by
  rw [endMatter_apply] at hne
  rw [Fock.secondQuant_card_eq ord _ (right_ne_zero_of_mul hne)]

theorem trace_conjTriplet (ρ : G →* Matrix C C ℂ) (g : G) :
    (Edge.conjTriplet ρ g).trace = conj (ρ g).trace := by
  simp [Edge.conjTriplet, Matrix.trace, map_sum]

/-- The trace of the matter of the string model at `(h, h)` on the tables with `k` dynamical
quarks: `Tr σ₀(h) Tr σ_R(h)` times the coefficient of `z^k` in `det(1 + z ρ(h))^{2d}`. -/
theorem sum_endMatter_diag (σ₀ σR ρ : G →* Matrix C C ℂ) (ord : LinearOrder (Edge.Mode C S))
    (k : ℕ) (h : G) :
    ∑ y ∈ Finset.univ.filter (fun y : (C × C) × Finset (Edge.Mode C S) => y.2.card = k),
        endMatter σ₀ σR ρ ord (h, h) y y =
      (σ₀ h).trace * (σR h).trace *
        ((1 + (X : ℂ[X]) • (ρ h).map Polynomial.C).det ^ (2 * Fintype.card S)).coeff k := by
  rw [← Edge.sum_numberSector_secondQuant_diag ord (ρ h) k, Finset.sum_filter,
    Finset.sum_filter, Fintype.sum_prod_type]
  have hterm : ∀ (x : C × C) (n : Finset (Edge.Mode C S)),
      (if n.card = k then endMatter σ₀ σR ρ ord (h, h) (x, n) (x, n) else 0) =
        (σ₀ h x.1 x.1 * σR h x.2 x.2) *
          (if n.card = k then Fock.secondQuant ord (Edge.diag (ρ h) (ρ h)) n n else 0) := by
    intro x n
    rw [endMatter_apply]
    split_ifs
    · rfl
    · rw [mul_zero]
  simp only [hterm, ← Finset.mul_sum, ← Finset.sum_mul]
  congr 1
  rw [Matrix.trace, Matrix.trace, Finset.sum_mul_sum, Fintype.sum_prod_type]
  rfl

end Count

end PathCanvas

/-! ### The key rotations: irreducibility and the commutant -/

namespace StringLine

/-- The half-turn about the first axis. -/
def H0 : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, -1, 0; 0, 0, -1]

/-- The half-turn about the second axis. -/
def H1 : Matrix (Fin 3) (Fin 3) ℂ := !![-1, 0, 0; 0, 1, 0; 0, 0, -1]

/-- The half-turn about the third axis. -/
def H2 : Matrix (Fin 3) (Fin 3) ℂ := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

/-- The third-turn that permutes the axes cyclically. -/
def T3 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

variable {G : Type*} [Group G]

/-- The image of the triplet contains the three half-turns about the axes and the third-turn. -/
def HasKey (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  (∃ g, ρ g = H0) ∧ (∃ g, ρ g = H1) ∧ (∃ g, ρ g = H2) ∧ ∃ g, ρ g = T3

/-- **The commutant.** A matrix that commutes with the half-turns and the third-turn is a
scalar. -/
theorem commutant {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ} (hk : HasKey ρ)
    (M : Matrix (Fin 3) (Fin 3) ℂ) (hM : ∀ g, ρ g * M = M * ρ g) : M = M 0 0 • 1 := by
  obtain ⟨⟨g0, h0⟩, ⟨g1, h1⟩, -, ⟨g3, h3⟩⟩ := hk
  have e0 := hM g0
  have e1 := hM g1
  have e3 := hM g3
  rw [h0] at e0
  rw [h1] at e1
  rw [h3] at e3
  have entry : ∀ (A B : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3), A = B → A i j = B i j :=
    fun A B i j h => by rw [h]
  have m01 : M 0 1 = -M 0 1 := by
    simpa [H0, Matrix.mul_apply, Fin.sum_univ_three] using entry _ _ 0 1 e0
  have m02 : M 0 2 = -M 0 2 := by
    simpa [H0, Matrix.mul_apply, Fin.sum_univ_three] using entry _ _ 0 2 e0
  have m10 : -M 1 0 = M 1 0 := by
    simpa [H0, Matrix.mul_apply, Fin.sum_univ_three] using entry _ _ 1 0 e0
  have m20 : -M 2 0 = M 2 0 := by
    simpa [H0, Matrix.mul_apply, Fin.sum_univ_three] using entry _ _ 2 0 e0
  have m12 : M 1 2 = -M 1 2 := by
    simpa [H1, Matrix.mul_apply, Fin.sum_univ_three] using entry _ _ 1 2 e1
  have m21 : -M 2 1 = M 2 1 := by
    simpa [H1, Matrix.mul_apply, Fin.sum_univ_three] using entry _ _ 2 1 e1
  have d1 : M 1 1 = M 0 0 := by
    simpa [T3, Matrix.mul_apply, Fin.sum_univ_three] using entry _ _ 0 1 e3
  have d2 : M 2 2 = M 1 1 := by
    simpa [T3, Matrix.mul_apply, Fin.sum_univ_three] using entry _ _ 1 2 e3
  have hdiag : ∀ i, (M 0 0 • (1 : Matrix (Fin 3) (Fin 3) ℂ)) i i = M 0 0 := fun i => by
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  have hoff : ∀ i j, i ≠ j → (M 0 0 • (1 : Matrix (Fin 3) (Fin 3) ℂ)) i j = 0 := fun i j h => by
    rw [Matrix.smul_apply, Matrix.one_apply_ne h, smul_zero]
  have z01 : M 0 1 = 0 := by linear_combination (1 / 2 : ℂ) * m01
  have z02 : M 0 2 = 0 := by linear_combination (1 / 2 : ℂ) * m02
  have z10 : M 1 0 = 0 := by linear_combination (-1 / 2 : ℂ) * m10
  have z20 : M 2 0 = 0 := by linear_combination (-1 / 2 : ℂ) * m20
  have z12 : M 1 2 = 0 := by linear_combination (1 / 2 : ℂ) * m12
  have z21 : M 2 1 = 0 := by linear_combination (-1 / 2 : ℂ) * m21
  ext i j
  fin_cases i <;> fin_cases j
  · exact (hdiag 0).symm
  · exact z01.trans (hoff 0 1 (by decide)).symm
  · exact z02.trans (hoff 0 2 (by decide)).symm
  · exact z10.trans (hoff 1 0 (by decide)).symm
  · exact d1.trans (hdiag 1).symm
  · exact z12.trans (hoff 1 2 (by decide)).symm
  · exact z20.trans (hoff 2 0 (by decide)).symm
  · exact z21.trans (hoff 2 1 (by decide)).symm
  · exact (d2.trans d1).trans (hdiag 2).symm

/-- The action of the triplet on vectors. -/
theorem tripletRep_apply (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ) (g : G) (v : Fin 3 → ℂ) :
    Edge.tripletRep ρ g v = ρ g *ᵥ v := rfl

/-- **Irreducibility.** A triplet whose image contains the half-turns and the third-turn is
irreducible: the half-turns project a nonzero invariant subspace onto an axis, and the third-turn
carries that axis to the others. -/
theorem irreducible {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ} (hk : HasKey ρ) :
    (Edge.tripletRep ρ).IsIrreducible := by
  obtain ⟨⟨g0, h0⟩, ⟨g1, h1⟩, ⟨g2, h2⟩, ⟨g3, h3⟩⟩ := hk
  have hhalf : ∀ i : Fin 3, ∃ g, ∀ w : Fin 3 → ℂ,
      ρ g *ᵥ w = fun j => if j = i then w j else -w j := by
    intro i
    fin_cases i
    · refine ⟨g0, fun w => ?_⟩
      rw [h0]
      funext j
      fin_cases j <;> simp [H0, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · refine ⟨g1, fun w => ?_⟩
      rw [h1]
      funext j
      fin_cases j <;> simp [H1, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · refine ⟨g2, fun w => ?_⟩
      rw [h2]
      funext j
      fin_cases j <;> simp [H2, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hthird : ∀ w : Fin 3 → ℂ, ρ g3 *ᵥ w = fun j => w (finRotate 3 j) := by
    intro w
    rw [h3]
    funext j
    fin_cases j <;> simp [T3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  · by_cases hW : ∀ v ∈ W.toSubmodule, v = 0
    · left
      apply Subrepresentation.toSubmodule_injective
      exact (Submodule.eq_bot_iff _).mpr hW
    · right
      push Not at hW
      obtain ⟨v, hv, hv0⟩ := hW
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra h
        push Not at h
        exact hv0 (funext h)
      obtain ⟨gi, hgi⟩ := hhalf i
      have hsingle : (Pi.single i 1 : Fin 3 → ℂ) ∈ W.toSubmodule := by
        have h1 := W.apply_mem_toSubmodule gi hv
        rw [tripletRep_apply, hgi] at h1
        have h2 := W.toSubmodule.add_mem hv h1
        have h3 := W.toSubmodule.smul_mem ((2 * v i)⁻¹) h2
        convert h3 using 1
        funext j
        simp only [Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        split_ifs with hj
        · subst hj
          field_simp
          ring
        · ring
      have hrot : ∀ j, (Pi.single j 1 : Fin 3 → ℂ) ∈ W.toSubmodule →
          (Pi.single ((finRotate 3).symm j) 1 : Fin 3 → ℂ) ∈ W.toSubmodule := by
        intro j hj
        have := W.apply_mem_toSubmodule g3 hj
        rw [tripletRep_apply, hthird] at this
        convert this using 1
        funext k
        simp only [Pi.single_apply, Equiv.eq_symm_apply]
      have hall : ∀ j, (Pi.single j 1 : Fin 3 → ℂ) ∈ W.toSubmodule := by
        intro j
        have h1 := hrot _ hsingle
        have h2 := hrot _ h1
        fin_cases i <;> fin_cases j <;> first | exact hsingle | exact h1 | exact h2
      apply Subrepresentation.toSubmodule_injective
      change W.toSubmodule = ⊤
      rw [eq_top_iff]
      intro w _
      have hw : w = ∑ j, w j • (Pi.single j 1 : Fin 3 → ℂ) := by
        funext k
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hw]
      exact W.toSubmodule.sum_mem fun j _ => W.toSubmodule.smul_mem _ (hall j)

/-! ### The string -/

open PathCanvas

variable {R : ℕ} {ρ : G →* Matrix (Fin 3) (Fin 3) ℂ}

/-- `(A ⊗ B) vec(M) = vec(A M Bᵀ)`. -/
theorem kron_mulVec (A B M : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix.kroneckerMap (· * ·) A B *ᵥ (fun x : Fin 3 × Fin 3 => M x.1 x.2) =
      fun x => (A * M * Bᵀ) x.1 x.2 := by
  funext x
  obtain ⟨c, c'⟩ := x
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.kroneckerMap_apply]
  ring

theorem sourcePair_apply (σ₀ σR : G →* Matrix (Fin 3) (Fin 3) ℂ) (h : G × G) :
    sourcePair σ₀ σR h = Matrix.kroneckerMap (· * ·) (σ₀ h.1) (σR h.2) := rfl

theorem string_apply (U : (Canvas.path R).skeleton.LinkTable G) (x : Fin 3 × Fin 3) :
    string R ρ U x = ρ (Skeleton.hol U (γ R))⁻¹ x.1 x.2 := rfl

/-- `(conj ρ(g))ᵀ = ρ(g)† = ρ(g⁻¹)` for a unitary triplet. -/
theorem conjTriplet_transpose (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ) (g : G) :
    (Edge.conjTriplet ρ g)ᵀ = ρ g⁻¹ := by
  rw [← Edge.star_eq_inv hunit]
  ext i j
  simp [Edge.conjTriplet, Matrix.star_apply]

/-- `ρ(g)ᵀ = ρ(g⁻¹)` for a real unitary triplet. -/
theorem transpose_of_real (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hreal : ∀ g i j, conj (ρ g i j) = ρ g i j) (g : G) : (ρ g)ᵀ = ρ g⁻¹ := by
  rw [← Edge.star_eq_inv hunit]
  ext i j
  simp [Matrix.star_apply, hreal]

/-- `ρ(P⁻¹)_{cc'} = conj(ρ(P)_{c'c})` for a unitary triplet. -/
theorem string_eq_conj (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (U : (Canvas.path R).skeleton.LinkTable G) (c c' : Fin 3) :
    string R ρ U (c, c') = conj (ρ (Skeleton.hol U (γ R)) c' c) := by
  rw [string_apply, ← Edge.star_eq_inv hunit, Matrix.star_apply]
  rfl

theorem hol_inv_gaugeAct (h : (Canvas.path R).V → G) (U : (Canvas.path R).skeleton.LinkTable G) :
    (Skeleton.hol (Skeleton.gaugeAct h U) (γ R))⁻¹ =
      h (x0 R) * (Skeleton.hol U (γ R))⁻¹ * (h (xR R))⁻¹ := by
  rw [Skeleton.hol_gaugeAct]
  group

/-- The string is a colourless state with a quark and an antiquark source. -/
theorem string_mem_conj (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    string R ρ ∈ colourless R (sourcePair ρ (Edge.conjTriplet ρ)) := by
  intro h U
  change (fun x : Fin 3 × Fin 3 => ρ (Skeleton.hol (Skeleton.gaugeAct h U) (γ R))⁻¹ x.1 x.2) =
    _ *ᵥ (fun x : Fin 3 × Fin 3 => ρ (Skeleton.hol U (γ R))⁻¹ x.1 x.2)
  rw [sourcePair_apply, kron_mulVec _ _ (ρ (Skeleton.hol U (γ R))⁻¹),
    conjTriplet_transpose hunit, hol_inv_gaugeAct, map_mul, map_mul]

/-- With a real triplet, the string is a colourless state with two quark sources. -/
theorem string_mem_real (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hreal : ∀ g i j, conj (ρ g i j) = ρ g i j) :
    string R ρ ∈ colourless R (sourcePair ρ ρ) := by
  intro h U
  change (fun x : Fin 3 × Fin 3 => ρ (Skeleton.hol (Skeleton.gaugeAct h U) (γ R))⁻¹ x.1 x.2) =
    _ *ᵥ (fun x : Fin 3 × Fin 3 => ρ (Skeleton.hol U (γ R))⁻¹ x.1 x.2)
  rw [sourcePair_apply, kron_mulVec _ _ (ρ (Skeleton.hol U (γ R))⁻¹),
    transpose_of_real hunit hreal, hol_inv_gaugeAct, map_mul, map_mul]

theorem string_ne_zero (hR : 0 < R) : string R ρ ≠ 0 := by
  intro h
  have := congrFun (congrFun h (std R 1)) (0, 0)
  rw [string_apply, hol_std R hR, inv_one, map_one] at this
  simp at this

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- A colourless state is `U ↦ Γ(1, P(U)) v` with `v` fixed by the diagonal pairs. -/
theorem colourless_val (hR : 0 < R) {Γ : G × G →* Matrix N N ℂ} {ψ}
    (hψ : ψ ∈ colourless R Γ) :
    (∀ U, ψ U = Γ (1, Skeleton.hol U (γ R)) *ᵥ ψ (std R 1)) ∧
      ∀ h, Γ (h, h) *ᵥ ψ (std R 1) = ψ (std R 1) := by
  obtain ⟨h1, h2⟩ := (Edge.mem_colourlessWith_iff Γ _).mp (toEdge_mem hR hψ)
  exact ⟨fun U => (eq_std hR hψ U).trans (h1 _), h2⟩

/-- A matrix fixed by `M ↦ ρ(g) M ρ(g)⁻¹` commutes with `ρ(g)`. -/
theorem commute_of_conj {g : G} {M : Matrix (Fin 3) (Fin 3) ℂ} (h : ρ g * M * ρ g⁻¹ = M) :
    ρ g * M = M * ρ g :=
  calc ρ g * M = ρ g * M * (ρ g⁻¹ * ρ g) := by
        rw [← map_mul, inv_mul_cancel, map_one, mul_one]
    _ = M * ρ g := by rw [← mul_assoc, h]

/-- The vector `v` of `C × C` as a matrix. -/
theorem vec_eq (v : Fin 3 × Fin 3 → ℂ) : v = fun x => (fun a b => v (a, b) :
    Matrix (Fin 3) (Fin 3) ℂ) x.1 x.2 := rfl

/-- **The line.** With a quark and an antiquark source, the colourless states are the multiples
of the string. -/
theorem colourless_conj_eq (hR : 0 < R) (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hk : HasKey ρ) :
    colourless R (sourcePair ρ (Edge.conjTriplet ρ)) = Submodule.span ℂ {string R ρ} := by
  apply le_antisymm
  · intro ψ hψ
    obtain ⟨hU, hfix⟩ := colourless_val hR hψ
    set v := ψ (std R 1) with hvdef
    set M : Matrix (Fin 3) (Fin 3) ℂ := fun a b => v (a, b) with hMdef
    have hv : v = fun x => M x.1 x.2 := rfl
    have hcomm : ∀ g, ρ g * M = M * ρ g := by
      intro g
      have hg := hfix g
      rw [sourcePair_apply, hv, kron_mulVec _ _ M, conjTriplet_transpose hunit] at hg
      refine commute_of_conj (Matrix.ext fun a b => ?_)
      exact congrFun hg (a, b)
    have hscalar := commutant hk M hcomm
    rw [Submodule.mem_span_singleton]
    refine ⟨M 0 0, ?_⟩
    funext U x
    rw [hU U, hv, sourcePair_apply, kron_mulVec _ _ M, map_one, conjTriplet_transpose hunit]
    change M 0 0 * string R ρ U x = _
    rw [string_apply, one_mul]
    conv_rhs => rw [hscalar]
    simp
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact string_mem_conj hunit

/-- **Two quark sources, a real triplet.** The colourless states are the multiples of the
string. -/
theorem colourless_real_eq (hR : 0 < R) (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hk : HasKey ρ) (hreal : ∀ g i j, conj (ρ g i j) = ρ g i j) :
    colourless R (sourcePair ρ ρ) = Submodule.span ℂ {string R ρ} := by
  apply le_antisymm
  · intro ψ hψ
    obtain ⟨hU, hfix⟩ := colourless_val hR hψ
    set v := ψ (std R 1) with hvdef
    set M : Matrix (Fin 3) (Fin 3) ℂ := fun a b => v (a, b) with hMdef
    have hv : v = fun x => M x.1 x.2 := rfl
    have hcomm : ∀ g, ρ g * M = M * ρ g := by
      intro g
      have hg := hfix g
      rw [sourcePair_apply, hv, kron_mulVec _ _ M, transpose_of_real hunit hreal] at hg
      refine commute_of_conj (Matrix.ext fun a b => ?_)
      exact congrFun hg (a, b)
    have hscalar := commutant hk M hcomm
    rw [Submodule.mem_span_singleton]
    refine ⟨M 0 0, ?_⟩
    funext U x
    rw [hU U, hv, sourcePair_apply, kron_mulVec _ _ M, map_one, transpose_of_real hunit hreal]
    change M 0 0 * string R ρ U x = _
    rw [string_apply, one_mul]
    conv_rhs => rw [hscalar]
    simp
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact string_mem_real hunit hreal

/-- `ω² ≠ 1`. -/
theorem omega_sq_ne_one : Exact.omega ^ 2 ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  rw [Exact.omega_sq] at him
  simp only [Complex.sub_im, Complex.neg_im, Complex.one_im, Exact.omega_im] at him
  have : Real.sqrt 3 = 0 := by linarith
  simp at this

/-- A matrix fixed by `M ↦ (ω 1) M (ω 1)ᵀ` is zero. -/
theorem eq_zero_of_omega {M : Matrix (Fin 3) (Fin 3) ℂ}
    (h : (Exact.omega • (1 : Matrix (Fin 3) (Fin 3) ℂ)) * M *
      (Exact.omega • (1 : Matrix (Fin 3) (Fin 3) ℂ))ᵀ = M) : M = 0 := by
  rw [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul, ← sq] at h
  have h2 : (Exact.omega ^ 2 - 1) • M = 0 := by rw [sub_smul, h, one_smul, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) omega_sq_ne_one
  · exact h3

/-- **Two quark sources, a complex triplet.** If `ω 1` is a matrix of the triplet, no colourless
state but zero has two quark sources. -/
theorem colourless_omega_eq (hR : 0 < R) {g₀ : G}
    (hg₀ : ρ g₀ = Exact.omega • (1 : Matrix (Fin 3) (Fin 3) ℂ)) :
    colourless R (sourcePair ρ ρ) = ⊥ := by
  rw [eq_bot_iff]
  intro ψ hψ
  obtain ⟨hU, hfix⟩ := colourless_val hR hψ
  set v := ψ (std R 1) with hvdef
  set M : Matrix (Fin 3) (Fin 3) ℂ := fun a b => v (a, b) with hMdef
  have hv : v = fun x => M x.1 x.2 := rfl
  have hM0 : M = 0 := by
    have hg := hfix g₀
    rw [sourcePair_apply, hv, kron_mulVec _ _ M] at hg
    refine eq_zero_of_omega (Matrix.ext fun a b => ?_)
    rw [← hg₀]
    exact congrFun hg (a, b)
  rw [Submodule.mem_bot]
  funext U x
  rw [hU U, hv, hM0, sourcePair_apply]
  simp [Matrix.mulVec, dotProduct]

/-- With a real triplet, the invariants of `3 ⊗ 3` are the multiples of `1`. -/
theorem pairInvariants_real (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ) (hk : HasKey ρ)
    (hreal : ∀ g i j, conj (ρ g i j) = ρ g i j) :
    pairInvariants ρ = Submodule.span ℂ {(1 : Matrix (Fin 3) (Fin 3) ℂ)} := by
  apply le_antisymm
  · intro T hT
    have hcomm : ∀ g, ρ g * T = T * ρ g := fun g =>
      commute_of_conj (by rw [← transpose_of_real hunit hreal]; exact hT g)
    rw [Submodule.mem_span_singleton]
    exact ⟨T 0 0, (commutant hk T hcomm).symm⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    intro g
    rw [Matrix.mul_one, transpose_of_real hunit hreal, ← map_mul, mul_inv_cancel, map_one]

theorem finrank_pairInvariants_real (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hk : HasKey ρ) (hreal : ∀ g i j, conj (ρ g i j) = ρ g i j) :
    Module.finrank ℂ ↥(pairInvariants ρ) = 1 := by
  rw [pairInvariants_real hunit hk hreal]
  exact finrank_span_singleton one_ne_zero

/-- With `ω 1` among the matrices of the triplet, `3 ⊗ 3` has no invariant. -/
theorem pairInvariants_omega {g₀ : G}
    (hg₀ : ρ g₀ = Exact.omega • (1 : Matrix (Fin 3) (Fin 3) ℂ)) : pairInvariants ρ = ⊥ := by
  rw [eq_bot_iff]
  intro T hT
  rw [Submodule.mem_bot]
  have := hT g₀
  rw [hg₀] at this
  exact eq_zero_of_omega this

/-! ### The tables of the links -/

theorem setLink_apply (U : (Canvas.path R).skeleton.LinkTable G) (j i : Fin R) (g : G) :
    (Canvas.path R).setLink U j g (i, true) = if i = j then g else U (i, true) := by
  simp only [Canvas.setLink, Skeleton.LinkTable.ofGraph, Function.update_apply]

theorem setLink_self (U : (Canvas.path R).skeleton.LinkTable G) (j : Fin R) :
    (Canvas.path R).setLink U j (U (j, true)) = U :=
  linkTable_ext fun i => by
    rw [setLink_apply]
    split_ifs with h
    · rw [h]
    · rfl

/-- The holonomy of the path with `g` on the link `j`: unchanged up to `x_j`, and
`(U_m ⋯ U_{j+2}) g (U_j ⋯ U_1)` beyond. -/
theorem hol_setLink_pathTo (U : (Canvas.path R).skeleton.LinkTable G) (j : Fin R) (g : G) :
    ∀ (m : ℕ) (hm : m < R + 1), Skeleton.hol ((Canvas.path R).setLink U j g) (pathTo R m hm) =
      if m ≤ j then Skeleton.hol U (pathTo R m hm) else
        Skeleton.hol U (pathTo R m hm) * (Skeleton.hol U (pathTo R (j + 1) (by omega)))⁻¹ * g *
          Skeleton.hol U (pathTo R j (by omega))
  | 0, hm => by
    rw [ite_eq_left (Nat.zero_le _)]
    rfl
  | m + 1, hm => by
    rw [hol_pathTo_succ, hol_pathTo_succ, setLink_apply, hol_setLink_pathTo U j g m (by omega)]
    by_cases hmj : m + 1 ≤ (j : ℕ)
    · have hne : (⟨m, by omega⟩ : Fin R) ≠ j := fun h => by
        rw [← h] at hmj
        simp at hmj
      rw [ite_eq_right hne, ite_eq_left (show m ≤ (j : ℕ) by omega), ite_eq_left hmj]
    · by_cases hmj' : m = (j : ℕ)
      · have hj : (⟨m, by omega⟩ : Fin R) = j := Fin.ext hmj'
        rw [ite_eq_left hj, ite_eq_left (show m ≤ (j : ℕ) by omega), ite_eq_right hmj]
        obtain ⟨j, hjR⟩ := j
        simp only at hmj'
        subst hmj'
        rw [hol_pathTo_succ]
        group
      · have hne : (⟨m, by omega⟩ : Fin R) ≠ j := fun h => hmj' (congrArg Fin.val h)
        rw [ite_eq_right hne, ite_eq_right (show ¬ m ≤ (j : ℕ) by omega), ite_eq_right hmj]
        group

/-- The holonomy of `γ` with `g` on the link `j` is `A g B`. -/
theorem hol_setLink (U : (Canvas.path R).skeleton.LinkTable G) (j : Fin R) (g : G) :
    Skeleton.hol ((Canvas.path R).setLink U j g) (γ R) =
      Skeleton.hol U (γ R) * (Skeleton.hol U (pathTo R (j + 1) (by omega)))⁻¹ * g *
        Skeleton.hol U (pathTo R j (by omega)) :=
  (hol_setLink_pathTo U j g R (Nat.lt_succ_self R)).trans (ite_eq_right (by omega))

/-- **On every link the string's table lies in the conjugate triplet block.** -/
theorem string_setLink_mem (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (U : (Canvas.path R).skeleton.LinkTable G) (j : Fin R) (c c' : Fin 3) :
    (fun g => string R ρ ((Canvas.path R).setLink U j g) (c, c')) ∈
      block (Edge.conjTripletRep ρ) := by
  set A := Skeleton.hol U (γ R) * (Skeleton.hol U (pathTo R (j + 1) (by omega)))⁻¹ with hA
  set B := Skeleton.hol U (pathTo R j (by omega)) with hB
  have hfun : (fun g => string R ρ ((Canvas.path R).setLink U j g) (c, c')) =
      ∑ a, ∑ b, (ρ B⁻¹ c a * ρ A⁻¹ b c') • fun g => conj (ρ g b a) := by
    funext g
    rw [string_apply, hol_setLink, ← hA, ← hB,
      show (A * g * B)⁻¹ = B⁻¹ * g⁻¹ * A⁻¹ by group, map_mul, map_mul,
      ← Edge.star_eq_inv hunit g]
    simp only [Matrix.mul_apply, Matrix.star_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [RCLike.star_def]
    ring
  rw [hfun]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (ThereAndBack.conj_entry_mem_block ρ b a)

/-- **One level per link.** An operator that multiplies the conjugate triplet block by `E₃`
multiplies the string by `E₃` on every link. -/
theorem onLink_string (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (X : (G → ℂ) → (G → ℂ)) (E₃ : ℚ)
    (hX : ∀ f ∈ block (Edge.conjTripletRep ρ), X f = (E₃ : ℂ) • f) (j : Fin R) :
    (Canvas.path R).onLink (liftTable X) j (string R ρ) = (E₃ : ℂ) • string R ρ := by
  funext U x
  obtain ⟨c, c'⟩ := x
  change X (fun g => string R ρ ((Canvas.path R).setLink U j g) (c, c')) (U (j, true)) = _
  rw [hX _ (string_setLink_mem hunit U j c c'), Pi.smul_apply, setLink_self]
  rfl

/-- The electric energy of the string is `κ E₃ R`. -/
theorem electric_string (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (X : (G → ℂ) → (G → ℂ)) (E₃ : ℚ)
    (hX : ∀ f ∈ block (Edge.conjTripletRep ρ), X f = (E₃ : ℂ) • f) (κ : ℝ) :
    (κ : ℂ) • electric R X (string R ρ) = ((κ * E₃ * R : ℝ) : ℂ) • string R ρ := by
  rw [electric, Finset.sum_congr rfl fun j _ => onLink_string hunit X E₃ hX j, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
  congr 1
  push_cast
  ring

/-- With a real triplet, the conjugate triplet block is the triplet block. -/
theorem block_conj_of_real (hreal : ∀ g i j, conj (ρ g i j) = ρ g i j) :
    block (Edge.conjTripletRep ρ) = block (Edge.tripletRep ρ) := by
  have h : Edge.conjTripletRep ρ = Edge.tripletRep ρ := by
    refine MonoidHom.ext fun g => ?_
    have hm : (ρ g).map (starRingEnd ℂ) = ρ g := by
      ext i j
      exact hreal g i j
    change Matrix.toLinAlgEquiv' ((ρ g).map (starRingEnd ℂ)) = Matrix.toLinAlgEquiv' (ρ g)
    rw [hm]
  rw [h]

/-- With `ω 1` among its matrices, the triplet is not real. -/
theorem not_real_of_omega {g₀ : G}
    (hg₀ : ρ g₀ = Exact.omega • (1 : Matrix (Fin 3) (Fin 3) ℂ)) :
    ¬ ∀ g i j, conj (ρ g i j) = ρ g i j := by
  intro h
  have h00 := h g₀ 0 0
  rw [hg₀] at h00
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
  have him := congrArg Complex.im h00
  rw [Complex.conj_im, Exact.omega_im] at him
  have : Real.sqrt 3 = 0 := by linarith
  simp at this

open Classical in
/-- **Theorem 13.2 for one colour group.** For a unitary triplet whose image contains the
half-turns and the third-turn, and which is real or contains `ω 1`. -/
theorem claims_of (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ) (hk : HasKey ρ)
    (hcase : (∀ g i j, conj (ρ g i j) = ρ g i j) ∨
      ∃ g₀, ρ g₀ = Exact.omega • (1 : Matrix (Fin 3) (Fin 3) ℂ)) :
    ∀ R : ℕ, 0 < R →
      colourless R (sourcePair ρ (Edge.conjTriplet ρ)) =
        Submodule.span ℂ {string R ρ} ∧
      string R ρ ≠ 0 ∧
      (∀ (U : (Canvas.path R).skeleton.LinkTable G) (c c' : Fin 3),
        string R ρ U (c, c') = conj (ρ (Skeleton.hol U (γ R)) c' c)) ∧
      (∀ (U : (Canvas.path R).skeleton.LinkTable G) (j : Fin R) (c c' : Fin 3),
        (fun g => string R ρ ((Canvas.path R).setLink U j g) (c, c')) ∈
          block (Edge.conjTripletRep ρ)) ∧
      ((∀ g i j, conj (ρ g i j) = ρ g i j) →
        block (Edge.conjTripletRep ρ) = block (Edge.tripletRep ρ)) ∧
      (∀ (X : (G → ℂ) → (G → ℂ)) (E₃ : ℚ) (κ : ℝ),
        (∀ f ∈ block (Edge.conjTripletRep ρ), X f = (E₃ : ℂ) • f) →
        (∀ j : Fin R, (Canvas.path R).onLink (liftTable X) j (string R ρ) =
          (E₃ : ℂ) • string R ρ) ∧
        (κ : ℂ) • electric R X (string R ρ) = ((κ * E₃ * R : ℝ) : ℂ) • string R ρ) ∧
      ((∃ ψ ∈ colourless R (sourcePair ρ ρ), ψ ≠ 0) ↔ ∀ g i j, conj (ρ g i j) = ρ g i j) ∧
      ((∀ g i j, conj (ρ g i j) = ρ g i j) →
        colourless R (sourcePair ρ ρ) = Submodule.span ℂ {string R ρ} ∧
        ∀ (U : (Canvas.path R).skeleton.LinkTable G) (c c' : Fin 3),
          string R ρ U (c, c') = ρ (Skeleton.hol U (γ R)) c' c) ∧
      (¬ (∀ g i j, conj (ρ g i j) = ρ g i j) → colourless R (sourcePair ρ ρ) = ⊥) ∧
      Module.finrank ℂ ↥(pairInvariants ρ) =
        if (∀ g i j, conj (ρ g i j) = ρ g i j) then 1 else 0 := by
  intro R hR
  have hreal_or : (∀ g i j, conj (ρ g i j) = ρ g i j) →
      colourless R (sourcePair ρ ρ) = Submodule.span ℂ {string R ρ} :=
    fun hreal => colourless_real_eq hR hunit hk hreal
  have hnotreal : ¬ (∀ g i j, conj (ρ g i j) = ρ g i j) → colourless R (sourcePair ρ ρ) = ⊥ := by
    intro hnr
    rcases hcase with hreal | ⟨g₀, hg₀⟩
    · exact absurd hreal hnr
    · exact colourless_omega_eq hR hg₀
  refine ⟨colourless_conj_eq hR hunit hk, string_ne_zero hR, string_eq_conj hunit,
    string_setLink_mem hunit, block_conj_of_real,
    fun X E₃ κ hX => ⟨onLink_string hunit X E₃ hX, electric_string hunit X E₃ hX κ⟩,
    ⟨fun ⟨ψ, hψ, hψ0⟩ => ?_, fun hreal => ⟨string R ρ, string_mem_real hunit hreal,
      string_ne_zero hR⟩⟩,
    fun hreal => ⟨hreal_or hreal, fun U c c' => ?_⟩, hnotreal, ?_⟩
  · by_contra hnr
    rw [hnotreal hnr, Submodule.mem_bot] at hψ
    exact hψ0 hψ
  · rw [string_eq_conj hunit, hreal]
  · by_cases hreal : ∀ g i j, conj (ρ g i j) = ρ g i j
    · rw [ite_eq_left hreal, finrank_pairInvariants_real hunit hk hreal]
    · rw [ite_eq_right hreal]
      rcases hcase with h | ⟨g₀, hg₀⟩
      · exact absurd h hreal
      · rw [pairInvariants_omega hg₀, finrank_bot]

/-- Convolution of a complex table by a kernel is the convolution matrix. -/
theorem tableConv_eq_convolution [Fintype G] (k ψ : G → ℂ) :
    tableConv k ψ = convolution k *ᵥ ψ := by
  funext V
  rw [Blocks.convolution_mulVec_apply, Blocks.sum_conv_eq_sum_leftWrite, Edge.tableConv_apply]
  simp only [leftWrite_apply, smul_eq_mul]

/-- The electric energy of Definition 11.9 multiplies the block of the conjugate triplet by its
declared level. -/
theorem electricEnergy_conj [Fintype G] (hirr : (Edge.tripletRep ρ).IsIrreducible)
    {ι : Type*} [Fintype ι] {d : ι → ℕ} {σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)}
    (hσ : IsCompleteFamily σ) (E : ι → ℚ) (E₃ : ℚ)
    (hE : ∀ i, Nonempty ((Edge.conjTripletRep ρ).Equiv (σ i)) → E i = E₃) :
    ∀ f ∈ block (Edge.conjTripletRep ρ), electricEnergy σ E f = (E₃ : ℂ) • f := by
  intro f hf
  obtain ⟨i, ⟨e⟩⟩ := hσ.2.2 3 (Edge.conjTripletRep ρ)
    (ThereAndBack.conjTripletRep_irreducible hirr)
  rw [← block_eq_of_equiv e] at hf
  rw [electricEnergy, ThereAndBack.energyKernel_eq_charComb, tableConv_eq_convolution,
    Blocks.convolution_charComb σ hσ.1 hσ.2.1 _ i hf, hE i ⟨e⟩]

/-! ### The five colour groups -/

open ColourGroups

theorem subTriplet_unit (H : Subgroup (Matrix.specialUnitaryGroup (Fin 3) ℂ)) (g : H) :
    subTriplet H g ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.mp (g : Matrix.specialUnitaryGroup (Fin 3) ℂ).2).1

theorem signed_H0 : signedPermMatrix 1 (fun j => if j = (0 : Fin 3) then 1 else -1) = H0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [signedPermMatrix, H0]

theorem signed_H1 : signedPermMatrix 1 (fun j => if j = (1 : Fin 3) then 1 else -1) = H1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [signedPermMatrix, H1]

theorem signed_H2 : signedPermMatrix 1 (fun j => if j = (2 : Fin 3) then 1 else -1) = H2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [signedPermMatrix, H2]

theorem signed_T3 : signedPermMatrix (finRotate 3) (fun _ => 1) = T3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [signedPermMatrix, T3]

theorem cube_key : HasKey cubeTriplet :=
  ⟨⟨CubeGroup.toGroup (CubeGroup.faceHalfTurnPair 0), signed_H0⟩,
    ⟨CubeGroup.toGroup (CubeGroup.faceHalfTurnPair 1), signed_H1⟩,
    ⟨CubeGroup.toGroup (CubeGroup.faceHalfTurnPair 2), signed_H2⟩,
    ⟨CubeGroup.toGroup CubeGroup.thirdTurnPair, signed_T3⟩⟩

theorem rotC_16 : rotC 16 = H0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotC, Icosahedron.R, Exact.M3.toRealHalf, Icosahedron.gE, Exact.ZPhi.toReal,
      Icosahedron.m, Icosahedron.v, H0]

theorem rotC_7 : rotC 7 = H1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotC, Icosahedron.R, Exact.M3.toRealHalf, Icosahedron.gE, Exact.ZPhi.toReal,
      Icosahedron.m, Icosahedron.v, H1]

theorem rotC_40 : rotC 40 = T3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotC, Icosahedron.R, Exact.M3.toRealHalf, Icosahedron.gE, Exact.ZPhi.toReal,
      Icosahedron.m, Icosahedron.v, T3]

theorem H0_mul_H1 : H0 * H1 = H2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H0, H1, H2, Matrix.mul_apply, Fin.sum_univ_three]

theorem ico_key : HasKey (subTriplet icoGroup) := by
  refine ⟨⟨icoElt 16, rotC_16⟩, ⟨icoElt 7, rotC_7⟩, ⟨icoElt 16 * icoElt 7, ?_⟩,
    ⟨icoElt 40, rotC_40⟩⟩
  rw [map_mul]
  change rotC 16 * rotC 7 = H2
  rw [rotC_16, rotC_7, H0_mul_H1]

theorem ico_real (g : icoGroup) (i j : Fin 3) :
    conj (subTriplet icoGroup g i j) = subTriplet icoGroup g i j := by
  obtain ⟨R, -, hR⟩ := g.2
  change conj (((g : Matrix.specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i j) = _
  change _ = ((g : Matrix.specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) i j
  rw [hR]
  simp

theorem c3a5_unit (x : C3A5) : c3a5Triplet x ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.mp (C3A5.triplet x).2).1

theorem c3a5Triplet_ico (k : Fin 60) :
    c3a5Triplet ((1 : Multiplicative (ZMod 3)), icoElt k) = rotC k := by
  simp [c3a5Triplet, C3A5.triplet, ZMod.val_zero]
  rfl

theorem c3a5_key : HasKey c3a5Triplet := by
  refine ⟨⟨(1, icoElt 16), by rw [c3a5Triplet_ico, rotC_16]⟩,
    ⟨(1, icoElt 7), by rw [c3a5Triplet_ico, rotC_7]⟩,
    ⟨(1, icoElt 16 * icoElt 7), ?_⟩, ⟨(1, icoElt 40), by rw [c3a5Triplet_ico, rotC_40]⟩⟩
  rw [show ((1 : Multiplicative (ZMod 3)), icoElt 16 * icoElt 7) =
    ((1 : Multiplicative (ZMod 3)), icoElt 16) * (1, icoElt 7) from rfl, map_mul,
    c3a5Triplet_ico, c3a5Triplet_ico, rotC_16, rotC_7, H0_mul_H1]

theorem c3a5_omega : ∃ x : C3A5, c3a5Triplet x = Exact.omega • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  obtain ⟨x, hx⟩ := C3A5_centre 1
  exact ⟨x, by rw [← pow_one Exact.omega]; exact hx⟩

/-- An element of `C₃ × A₅` as an element of Valentiner's group. -/
noncomputable def valOf (x : C3A5) : valentiner :=
  ⟨C3A5.triplet x, Subgroup.subset_closure (Set.mem_union_left _ ⟨x, rfl⟩)⟩

theorem subTriplet_valOf (x : C3A5) : subTriplet valentiner (valOf x) = c3a5Triplet x := rfl

theorem val_key : HasKey (subTriplet valentiner) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨e, he⟩⟩ := c3a5_key
  exact ⟨⟨valOf a, ha⟩, ⟨valOf b, hb⟩, ⟨valOf c, hc⟩, ⟨valOf e, he⟩⟩

theorem val_omega : ∃ g : valentiner,
    subTriplet valentiner g = Exact.omega • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  obtain ⟨x, hx⟩ := c3a5_omega
  exact ⟨valOf x, hx⟩

theorem su3_unit (g : Matrix.specialUnitaryGroup (Fin 3) ℂ) :
    su3Triplet g ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1

theorem su3_key : HasKey su3Triplet := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨e, he⟩⟩ := cube_key
  exact ⟨⟨(a : Matrix.specialUnitaryGroup (Fin 3) ℂ), ha⟩,
    ⟨(b : Matrix.specialUnitaryGroup (Fin 3) ℂ), hb⟩,
    ⟨(c : Matrix.specialUnitaryGroup (Fin 3) ℂ), hc⟩,
    ⟨(e : Matrix.specialUnitaryGroup (Fin 3) ℂ), he⟩⟩

theorem su3_omega : ∃ g : Matrix.specialUnitaryGroup (Fin 3) ℂ,
    su3Triplet g = Exact.omega • (1 : Matrix (Fin 3) (Fin 3) ℂ) :=
  ⟨⟨Exact.omega ^ 1 • 1, omega_pow_smul_mem 1 (Submonoid.one_mem _)⟩, by
    change Exact.omega ^ 1 • (1 : Matrix (Fin 3) (Fin 3) ℂ) = _
    rw [pow_one]⟩

/-! ### The pair moment `⟨χ²⟩` of the four finite groups -/

theorem cube_square : ∑ k : Fin 24, Exact.M3Z.trace (cubeE k) ^ 2 = ⟨24, 0, 0, 0⟩ := by
  decide +kernel

theorem cube_avg_sq : groupAvg cubeGroup (fun g => (cubeTriplet g).trace ^ 2) = 1 := by
  rw [show (fun g => (cubeTriplet g).trace ^ 2) = fun g => colourChar cubeGroup g ^ 2 from rfl,
    groupAvg_cubeGroup]
  have e : ∑ k : Fin 24, colourChar cubeGroup (cubeElt k) ^ 2 =
      Exact.ZOP.toComplex (∑ k : Fin 24, Exact.M3Z.trace (cubeE k) ^ 2) := by
    rw [toComplex_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [char_cubeElt, Exact.ZOP.toComplex_pow]
  rw [e, cube_square]
  simp [Exact.ZOP.toComplex]

theorem a5_square : zsum (fun n => trA5 n ^ 2) 60 = ⟨240, 0, 0, 0⟩ := by
  decide +kernel

theorem ico_avg_sq : groupAvg icoGroup (fun g => (subTriplet icoGroup g).trace ^ 2) = 1 := by
  rw [show (fun g => (subTriplet icoGroup g).trace ^ 2) = fun g => colourChar icoGroup g ^ 2 from
    rfl, groupAvg_icoGroup]
  have e : ∑ n ∈ Finset.range 60, colourChar icoGroup (icoEltN n) ^ 2 =
      Exact.ZOP.toComplex (zsum (fun n => trA5 n ^ 2) 60) / 4 := by
    rw [toComplex_zsum, Finset.sum_div]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_range] at hn
    rw [icoEltN_eq n hn, char_icoElt, Exact.ZOP.toComplex_pow]
    ring
  rw [e, a5_square]
  simp [Exact.ZOP.toComplex]
  norm_num

theorem sum_omega_sq : ∑ j : Multiplicative (ZMod 3),
    (Exact.omega ^ (Multiplicative.toAdd j).val) ^ 2 = 0 := by
  rw [show (∑ j : Multiplicative (ZMod 3), (Exact.omega ^ (Multiplicative.toAdd j).val) ^ 2) =
    ∑ a : Fin 3, (Exact.omega ^ (a : ℕ)) ^ 2 from rfl, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, one_pow, pow_one]
  linear_combination (Exact.omega ^ 2 - Exact.omega + 1) * Exact.omega_sq_add

theorem c3a5_avg_sq : groupAvg C3A5 (fun x => (c3a5Triplet x).trace ^ 2) = 0 := by
  have hchar : ∀ x : C3A5, (c3a5Triplet x).trace ^ 2 =
      (Exact.omega ^ (Multiplicative.toAdd x.1).val) ^ 2 * colourChar icoGroup x.2 ^ 2 := by
    intro x
    rw [show (c3a5Triplet x).trace = C3A5.char x from rfl, char_C3A5, mul_pow]
  rw [groupAvg, finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
  simp only [hchar, ← Finset.mul_sum, ← Finset.sum_mul, sum_omega_sq, zero_mul, mul_zero]

theorem val_square : classSum (fun t => t * t) = ⟨0, 0, 0, 0⟩ := by
  decide +kernel

theorem val_avg_sq : groupAvg valentiner (fun g => (subTriplet valentiner g).trace ^ 2) = 0 := by
  rw [show (fun g => (subTriplet valentiner g).trace ^ 2) =
    fun g => (fun z : ℂ => z ^ 2) (colourChar valentiner g) from rfl,
    avg_exact (fun z => z ^ 2) (fun t => t * t)
      (fun t => by rw [Exact.ZOP.toComplex_mul, sq]) 0 val_square]
  simp

/-! ### Levels of the string model (Proposition 13.4) -/

section Levels

variable {N : Type*}

/-- An operator that multiplies the conjugate triplet block by `E₃` multiplies by `E₃` every state
whose link tables lie in that block. -/
theorem onLink_of_mem_block (X : (G → ℂ) → (G → ℂ)) (E₃ : ℚ)
    (hX : ∀ f ∈ block (Edge.conjTripletRep ρ), X f = (E₃ : ℂ) • f)
    (ψ : (Canvas.path R).skeleton.LinkTable G → N → ℂ)
    (hψ : ∀ U (j : Fin R) x, (fun g => ψ ((Canvas.path R).setLink U j g) x) ∈
      block (Edge.conjTripletRep ρ)) (j : Fin R) :
    (Canvas.path R).onLink (liftTable X) j ψ = (E₃ : ℂ) • ψ := by
  funext U x
  change X (fun g => ψ ((Canvas.path R).setLink U j g) x) (U (j, true)) = _
  rw [hX _ (hψ U j x), Pi.smul_apply, setLink_self]
  rfl

/-- An operator that kills the constant tables kills the electric energy of a state constant in
the link table. -/
theorem electric_of_const (X : (G → ℂ) → (G → ℂ)) (hX : ∀ c : ℂ, X (fun _ => c) = 0)
    (ψ : (Canvas.path R).skeleton.LinkTable G → N → ℂ) (hψ : ∀ U V, ψ U = ψ V) :
    electric R X ψ = 0 := by
  rw [electric]
  refine Finset.sum_eq_zero fun j _ => ?_
  funext U x
  change X (fun g => ψ ((Canvas.path R).setLink U j g) x) (U (j, true)) = 0
  rw [show (fun g => ψ ((Canvas.path R).setLink U j g) x) = fun _ => ψ U x from
    funext fun g => by rw [hψ _ U], hX]
  rfl

variable {S : Type*} [DecidableEq S]

theorem stringState_apply (U : (Canvas.path R).skeleton.LinkTable G)
    (x : (Fin 3 × Fin 3) × Finset (Edge.Mode (Fin 3) S)) :
    stringState R ρ U x = if x.2 = ∅ then string R ρ U x.1 else 0 := rfl

theorem stringState_mem_block (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (U : (Canvas.path R).skeleton.LinkTable G) (j : Fin R)
    (x : (Fin 3 × Fin 3) × Finset (Edge.Mode (Fin 3) S)) :
    (fun g => stringState R ρ ((Canvas.path R).setLink U j g) x) ∈
      block (Edge.conjTripletRep ρ) := by
  by_cases hx : x.2 = ∅
  · simp only [stringState_apply, hx, ite_true]
    exact string_setLink_mem hunit U j x.1.1 x.1.2
  · simp only [stringState_apply, hx, ite_false]
    exact (block (Edge.conjTripletRep ρ)).zero_mem

theorem electric_stringState (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (X : (G → ℂ) → (G → ℂ)) (E₃ : ℚ)
    (hX : ∀ f ∈ block (Edge.conjTripletRep ρ), X f = (E₃ : ℂ) • f) :
    electric R X (stringState (S := S) R ρ) =
      ((E₃ * R : ℝ) : ℂ) • stringState (S := S) R ρ := by
  rw [electric, Finset.sum_congr rfl fun j _ =>
    onLink_of_mem_block X E₃ hX _ (stringState_mem_block hunit) j, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  push_cast
  ring

theorem mass_stringState (M : ℝ) : mass R M (stringState (S := S) R ρ) = 0 := by
  funext U x
  change ((M : ℂ) * x.2.card) * stringState R ρ U x = 0
  by_cases hx : x.2 = ∅
  · rw [hx, Finset.card_empty]
    simp
  · rw [stringState_apply, ite_eq_right hx, mul_zero]

omit [DecidableEq S] in
theorem mass_of_mem (M : ℝ) (k : ℕ) {ψ : (Canvas.path R).skeleton.LinkTable G →
    (Fin 3 × Fin 3) × Finset (Edge.Mode (Fin 3) S) → ℂ} (hψ : ψ ∈ quarkSector R k) :
    mass R M ψ = ((k * M : ℝ) : ℂ) • ψ := by
  funext U x
  change ((M : ℂ) * x.2.card) * ψ U x = ((k * M : ℝ) : ℂ) * ψ U x
  by_cases h0 : ψ U x = 0
  · rw [h0, mul_zero, mul_zero]
  · rw [hψ U x h0]
    push_cast
    ring

theorem stringState_ne_zero (hR : 0 < R) : stringState (S := S) R ρ ≠ 0 := by
  intro h
  have := congrFun (congrFun h (std R 1)) ((0, 0), ∅)
  rw [stringState_apply, ite_eq_left rfl, string_apply, hol_std R hR, inv_one, map_one] at this
  simp at this

theorem stringState_mem_sector : stringState (S := S) R ρ ∈ quarkSector R 0 := by
  intro U x hx
  rw [stringState_apply] at hx
  by_cases h : x.2 = ∅
  · rw [h, Finset.card_empty]
  · exact absurd (ite_eq_right h) hx

end Levels

/-! ### The hop keeps the number of quarks -/

section Hop

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

theorem creation_mul_annihilation_card {M : Type*} [Fintype M] [DecidableEq M]
    (ord : LinearOrder M) (m m' : M) {n' n : Finset M}
    (h : (Fock.creation ord m * Fock.annihilation ord m') n' n ≠ 0) : n'.card = n.card := by
  rw [Matrix.mul_apply] at h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 := left_ne_zero_of_mul hk
  have h2 := right_ne_zero_of_mul hk
  simp only [Fock.creation, Fock.annihilation, Matrix.of_apply] at h1 h2
  split_ifs at h1 h2 with hc ha
  · obtain ⟨hmk, rfl⟩ := hc
    obtain ⟨hmn, rfl⟩ := ha
    rw [Finset.card_insert_of_notMem hmk, Finset.card_erase_of_mem hmn]
    have : 0 < n.card := Finset.card_pos.mpr ⟨m', hmn⟩
    omega
  · exact absurd rfl h2
  · exact absurd rfl h1
  · exact absurd rfl h1

/-- **The hop conserves the quark number.** -/
theorem hopAt_card (ord : LinearOrder (Edge.Mode C S)) (u : Matrix C C ℂ)
    {n' n : Finset (Edge.Mode C S)} (h : Edge.hopAt ord u n' n ≠ 0) : n'.card = n.card := by
  rw [Edge.hopAt, Matrix.add_apply] at h
  have hor : ∀ a b : ℂ, a + b ≠ 0 → a ≠ 0 ∨ b ≠ 0 := fun a b hab => by
    by_contra hc
    simp only [not_or, not_not] at hc
    rw [hc.1, hc.2, add_zero] at hab
    exact hab rfl
  rcases hor _ _ h with h | h
  all_goals
    obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by simpa [Matrix.sum_apply] using h)
    obtain ⟨c', -, hc'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
    obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc'
    exact creation_mul_annihilation_card ord _ _ (right_ne_zero_of_mul hs)

theorem hop_mem_sector {G : Type*} [Group G] (ρ : G →* Matrix C C ℂ)
    (ord : LinearOrder (Edge.Mode C S)) (k : ℕ) (ψ : G → Finset (Edge.Mode C S) → ℂ)
    (hψ : ψ ∈ Edge.stateSector G (Fock.numberSector (Edge.Mode C S) k)) :
    Edge.hop ρ ord ψ ∈ Edge.stateSector G (Fock.numberSector (Edge.Mode C S) k) := by
  refine Submodule.mem_pi.mpr fun U _ => ?_
  have hU := Submodule.mem_pi.mp hψ U (Set.mem_univ _)
  exact Fock.mulVec_mem_of_respects (Edge.hopAt ord (ρ U)) (fun n => n.card = k)
    (fun n' n hne => by rw [hopAt_card ord (ρ U) hne]) hU

end Hop

/-! ### Definition 11.9 on the trivial block -/

/-- An irreducible representation with a nonzero invariant vector is trivial. -/
theorem isTrivial_of_invariants {V : Type*} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ G V) [τ.IsIrreducible] (h : τ.invariants ≠ ⊥) : τ.IsTrivial := by
  let W : Subrepresentation τ := ⟨τ.invariants, fun g v hv => by
    rw [Representation.mem_invariants] at hv ⊢
    intro g'
    rw [hv g, hv g']⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top W with hW | hW
  · exact absurd (congrArg Subrepresentation.toSubmodule hW) h
  · refine ⟨fun g => LinearMap.ext fun v => ?_⟩
    have hv : v ∈ W.toSubmodule := by
      rw [show W.toSubmodule = (⊤ : Subrepresentation τ).toSubmodule from
        congrArg Subrepresentation.toSubmodule hW]
      exact Submodule.mem_top
    exact hv g

/-- The electric energy of Definition 11.9 kills the constant tables: the kernel sums to the
level of the trivial block, `0`. -/
theorem electricEnergy_const [Fintype G] {ι : Type*} [Fintype ι] {d : ι → ℕ}
    {σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ)} (hσ : IsCompleteFamily σ) (E : ι → ℚ)
    (hE : IsEnergyTable σ E) (c : ℂ) : electricEnergy σ E (fun _ : G => c) = 0 := by
  have hsum : ∀ i, (E i : ℂ) * d i * ∑ h, (σ i).character h = 0 := by
    intro i
    by_cases ht : (σ i).IsTrivial
    · rw [(hE i).1 ht]
      simp
    · have := hσ.1 i
      have hinv : (σ i).invariants = ⊥ := by
        by_contra hne
        exact ht (isTrivial_of_invariants (σ i) hne)
      have hcard : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
      have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard
      have havg := Representation.card_inv_mul_sum_char_eq_finrank (σ i)
      rw [hinv, finrank_bot, Nat.cast_zero] at havg
      have : ∑ h, (σ i).character h = 0 := by
        have h2 := congrArg (fun z => (Nat.card G : ℂ) * z) havg
        simp only [mul_zero] at h2
        rw [← h2, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
      rw [this, mul_zero]
  funext V
  rw [electricEnergy, Edge.tableConv_apply]
  simp only [smul_eq_mul, Pi.zero_apply]
  rw [← Finset.sum_mul]
  have hk : ∑ h, responseKernel (fun i => (σ i).character) (fun i => (d i : ℂ))
      (fun i => (E i : ℂ)) h = 0 := by
    simp only [responseKernel, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hsum, Finset.sum_const_zero, mul_zero]
  rw [hk, zero_mul]

open Classical in
/-- **Proposition 13.4 for one colour group.** -/
theorem breaking_of (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    (∀ (X : (G → ℂ) → (G → ℂ)) (E₃ : ℚ),
      (∀ f ∈ block (Edge.conjTripletRep ρ), X f = (E₃ : ℂ) • f) → (∀ c : ℂ, X (fun _ => c) = 0) →
      ∀ (ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2))) (R : ℕ), 0 < R → ∀ κ M : ℝ, 0 < κ →
        0 ≤ M →
        let H := fun ψ : (Canvas.path R).skeleton.LinkTable G →
            (Fin 3 × Fin 3) × Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ =>
          (κ : ℂ) • electric R X ψ + mass R M ψ
        let Z := zeroFlux R (endMatter ρ (Edge.conjTriplet ρ) ρ ord) ⊓
          quarkSector R (if (∀ g i j, conj (ρ g i j) = ρ g i j) then 2 else 3)
        H (stringState R ρ) = ((κ * E₃ * R : ℝ) : ℂ) • stringState R ρ ∧
        (∀ ψ ∈ Z, H ψ = (((if (∀ g i j, conj (ρ g i j) = ρ g i j) then 2 else 3 : ℕ) * M : ℝ) :
          ℂ) • ψ) ∧
        (∀ ψ ∈ Z, ψ ≠ 0 → ∀ lstr lscr : ℝ,
          H (stringState R ρ) = (lstr : ℂ) • stringState R ρ →
          H ψ = (lscr : ℂ) • ψ →
            (lstr < lscr ↔ κ * E₃ * R <
              (if (∀ g i j, conj (ρ g i j) = ρ g i j) then 2 else 3 : ℕ) * M) ∧
            (lscr < lstr ↔
              (if (∀ g i j, conj (ρ g i j) = ρ g i j) then 2 else 3 : ℕ) * M < κ * E₃ * R)) ∧
        (E₃ = 4 / 3 → ((κ * E₃ * R =
            (if (∀ g i j, conj (ρ g i j) = ρ g i j) then 2 else 3 : ℕ) * M) ↔
          (R : ℝ) = if (∀ g i j, conj (ρ g i j) = ρ g i j) then 3 * M / (2 * κ)
            else 9 * M / (4 * κ))) ∧
        stringState (S := Fin 2) R ρ ∈ quarkSector R 0 ∧
        Z ≤ quarkSector R (if (∀ g i j, conj (ρ g i j) = ρ g i j) then 2 else 3) ∧
        (if (∀ g i j, conj (ρ g i j) = ρ g i j) then 2 else 3 : ℕ) ≠ 0) ∧
    ∀ (S : Type) [Fintype S] [DecidableEq S] (ord : LinearOrder (Edge.Mode (Fin 3) S)) (k : ℕ),
      ∀ ψ ∈ Edge.stateSector G (Fock.numberSector (Edge.Mode (Fin 3) S) k),
        Edge.hop ρ ord ψ ∈ Edge.stateSector G (Fock.numberSector (Edge.Mode (Fin 3) S) k) := by
  refine ⟨fun X E₃ hX hX0 ord R hR κ M hκ hM => ?_,
    fun S _ _ ord k ψ hψ => hop_mem_sector ρ ord k ψ hψ⟩
  set kmin : ℕ := if (∀ g i j, conj (ρ g i j) = ρ g i j) then 2 else 3 with hkmin
  intro H Z
  have hstr : H (stringState R ρ) = ((κ * E₃ * R : ℝ) : ℂ) • stringState R ρ := by
    change (κ : ℂ) • electric R X (stringState R ρ) + mass R M (stringState R ρ) = _
    rw [electric_stringState hunit X E₃ hX, mass_stringState, add_zero, smul_smul]
    congr 1
    push_cast
    ring
  have hscr : ∀ ψ ∈ Z, H ψ = ((kmin * M : ℝ) : ℂ) • ψ := by
    intro ψ hψ
    obtain ⟨⟨-, hconst⟩, hsec⟩ := hψ
    change (κ : ℂ) • electric R X ψ + mass R M ψ = _
    rw [electric_of_const X hX0 ψ hconst, smul_zero, zero_add, mass_of_mem M kmin hsec]
  refine ⟨hstr, hscr, fun ψ hψ hψ0 lstr lscr h1 h2 => ?_, fun hE => ?_,
    stringState_mem_sector, inf_le_right, by rw [hkmin]; split_ifs <;> norm_num⟩
  · have e1 : (lstr : ℂ) = ((κ * E₃ * R : ℝ) : ℂ) :=
      smul_left_injective ℂ (stringState_ne_zero hR) (h1.symm.trans hstr)
    have e2 : (lscr : ℂ) = ((kmin * M : ℝ) : ℂ) :=
      smul_left_injective ℂ hψ0 (h2.symm.trans (hscr ψ hψ))
    rw [Complex.ofReal_inj] at e1 e2
    rw [e1, e2]
    exact ⟨Iff.rfl, Iff.rfl⟩
  · rw [hE]
    push_cast
    by_cases hreal : ∀ g i j, conj (ρ g i j) = ρ g i j
    · rw [hkmin, ite_eq_left hreal, ite_eq_left hreal]
      push_cast
      constructor
      · intro h
        field_simp
        linarith
      · intro h
        rw [h]
        field_simp
        ring
    · rw [hkmin, ite_eq_right hreal, ite_eq_right hreal]
      push_cast
      constructor
      · intro h
        field_simp
        linarith
      · intro h
        rw [h]
        field_simp
        ring

/-! ### Zero flux at the two ends (Proposition 13.3) -/

section ZeroFlux

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- A zero-flux state is constant, with a value fixed by every gauge pair. -/
theorem mem_zeroFlux_iff (hR : 0 < R) (Γ : G × G →* Matrix N N ℂ)
    (ψ : (Canvas.path R).skeleton.LinkTable G → N → ℂ) :
    ψ ∈ zeroFlux R Γ ↔ (∀ U, ψ U = ψ (std R 1)) ∧ ∀ h, Γ h *ᵥ ψ (std R 1) = ψ (std R 1) := by
  constructor
  · rintro ⟨hc, hconst⟩
    refine ⟨fun U => hconst U _, fun h => ?_⟩
    have := hc (endChange R h.1 h.2) (std R 1)
    rw [endChange_x0 R hR, endChange_xR, hconst _ (std R 1)] at this
    exact this.symm
  · rintro ⟨hconst, hfix⟩
    refine ⟨fun h U => ?_, fun U V => by rw [hconst U, hconst V]⟩
    rw [hconst, hconst U, hfix]

/-- The constant states, as a linear map. -/
def constLin : (N → ℂ) →ₗ[ℂ] ((Canvas.path R).skeleton.LinkTable G → N → ℂ) where
  toFun v := constState R v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype N] [DecidableEq N] in
theorem constLin_injective : Function.Injective (constLin (R := R) (G := G) (N := N)) :=
  fun _ _ h => congrFun h (std R 1)

/-- The zero-flux states with values in `Z` are the constant states of the fixed vectors of
`Z`. -/
theorem zeroFlux_inf_eq (hR : 0 < R) (Γ : G × G →* Matrix N N ℂ) (Z : Submodule ℂ (N → ℂ)) :
    zeroFlux R Γ ⊓ Submodule.pi Set.univ
        (fun _ : (Canvas.path R).skeleton.LinkTable G => Z) =
      (Z ⊓ Fock.fixedSub Γ).map constLin := by
  ext ψ
  simp only [Submodule.mem_inf, Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨hψ, hZ⟩
    obtain ⟨hconst, hfix⟩ := (mem_zeroFlux_iff hR Γ ψ).mp hψ
    exact ⟨ψ (std R 1), ⟨hZ _, hfix⟩, funext fun U => (hconst U).symm⟩
  · rintro ⟨v, ⟨hvZ, hvfix⟩, rfl⟩
    exact ⟨(mem_zeroFlux_iff hR Γ _).mpr ⟨fun _ => rfl, hvfix⟩, fun _ => hvZ⟩

theorem finrank_zeroFlux_inf (hR : 0 < R) (Γ : G × G →* Matrix N N ℂ)
    (Z : Submodule ℂ (N → ℂ)) :
    Module.finrank ℂ ↥(zeroFlux R Γ ⊓ Submodule.pi Set.univ
        (fun _ : (Canvas.path R).skeleton.LinkTable G => Z)) =
      Module.finrank ℂ ↥(Z ⊓ Fock.fixedSub Γ) := by
  rw [zeroFlux_inf_eq hR]
  exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ constLin_injective _).symm

end ZeroFlux

/-! ### Counting the zero-flux states at the ends -/

section Counting

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The vectors of the matter at the ends with `k` dynamical quarks. -/
def sectorVec (S : Type*) (k : ℕ) :
    Submodule ℂ ((Fin 3 × Fin 3) × Finset (Edge.Mode (Fin 3) S) → ℂ) where
  carrier := {v | ∀ y, v y ≠ 0 → y.2.card = k}
  add_mem' {v w} hv hw y hy := by
    by_cases h : v y = 0
    · exact hw y (by simpa [h] using hy)
    · exact hv y h
  zero_mem' y hy := absurd rfl hy
  smul_mem' c v hv y hy := hv y (right_ne_zero_of_mul hy)

omit [Fintype S] [DecidableEq S] in
theorem quarkSector_eq (k : ℕ) :
    quarkSector (G := G) (C := Fin 3) (S := S) R k =
      Submodule.pi Set.univ (fun _ : (Canvas.path R).skeleton.LinkTable G => sectorVec S k) := by
  ext ψ
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies]
  rfl

/-- The trace of the matter of the string model at a gauge pair on the vectors with `k` quarks. -/
theorem sum_endMatter (σ₀ σR : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (ord : LinearOrder (Edge.Mode (Fin 3) S)) (k : ℕ) (h : G × G) :
    ∑ y ∈ Finset.univ.filter (fun y : (Fin 3 × Fin 3) × Finset (Edge.Mode (Fin 3) S) =>
        y.2.card = k), endMatter σ₀ σR ρ ord h y y =
      (σ₀ h.1).trace * (σR h.2).trace *
        ((1 + (X : ℂ[X]) • (ρ h.1).map Polynomial.C).det ^ Fintype.card S *
          (1 + (X : ℂ[X]) • (ρ h.2).map Polynomial.C).det ^ Fintype.card S).coeff k := by
  have hW : ∑ n ∈ Finset.univ.filter (fun n : Finset (Edge.Mode (Fin 3) S) => n.card = k),
      Edge.pairHom ρ ord h n n =
      ((1 + (X : ℂ[X]) • (ρ h.1).map Polynomial.C).det ^ Fintype.card S *
        (1 + (X : ℂ[X]) • (ρ h.2).map Polynomial.C).det ^ Fintype.card S).coeff k := by
    rw [Edge.filter_card_eq_powersetCard,
      show Edge.pairHom ρ ord h = Fock.secondQuant ord (Edge.diag (ρ h.1) (ρ h.2)) from rfl,
      Fock.sum_powersetCard_secondQuant_diag, Edge.det_one_add_X_smul_diag]
  rw [← hW, Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type]
  have hterm : ∀ (x : Fin 3 × Fin 3) (n : Finset (Edge.Mode (Fin 3) S)),
      (if n.card = k then endMatter σ₀ σR ρ ord h (x, n) (x, n) else 0) =
        (σ₀ h.1 x.1 x.1 * σR h.2 x.2 x.2) *
          (if n.card = k then Edge.pairHom ρ ord h n n else 0) := by
    intro x n
    rw [endMatter_apply]
    split_ifs
    · rfl
    · rw [mul_zero]
  simp only [hterm, ← Finset.mul_sum, ← Finset.sum_mul]
  congr 1
  rw [Matrix.trace, Matrix.trace, Finset.sum_mul_sum, Fintype.sum_prod_type]
  rfl

omit [Group G] in
/-- The average over the gauge pairs factorizes into the averages over each end. -/
theorem average_pairs [Fintype G] (a b : G → ℂ) (P : G → ℂ[X]) (k : ℕ) :
    (Fintype.card (G × G) : ℂ)⁻¹ * ∑ h : G × G, a h.1 * b h.2 * (P h.1 * P h.2).coeff k =
      (((Fintype.card G : ℂ)⁻¹ • ∑ g, Polynomial.C (a g) * P g) *
        ((Fintype.card G : ℂ)⁻¹ • ∑ g, Polynomial.C (b g) * P g)).coeff k := by
  rw [smul_mul_smul_comm, Polynomial.coeff_smul, Finset.sum_mul_sum,
    Polynomial.finsetSum_coeff, Fintype.card_prod, Fintype.sum_prod_type, smul_eq_mul]
  push_cast
  rw [mul_inv]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun g' _ => ?_
  rw [show Polynomial.C (a g) * P g * (Polynomial.C (b g') * P g') =
    Polynomial.C (a g * b g') * (P g * P g') by rw [map_mul]; ring, Polynomial.coeff_C_mul]

/-- The coefficients of `(1 + a z + b z² + z³)²`. -/
theorem coeff_cubic_sq (a b : ℂ) :
    ((1 + Polynomial.C a * X + Polynomial.C b * X ^ 2 + X ^ 3) ^ 2 : ℂ[X]).coeff 0 = 1 ∧
    ((1 + Polynomial.C a * X + Polynomial.C b * X ^ 2 + X ^ 3) ^ 2 : ℂ[X]).coeff 1 = 2 * a ∧
    ((1 + Polynomial.C a * X + Polynomial.C b * X ^ 2 + X ^ 3) ^ 2 : ℂ[X]).coeff 2 =
      a ^ 2 + 2 * b := by
  have e : ((1 + Polynomial.C a * X + Polynomial.C b * X ^ 2 + X ^ 3) ^ 2 : ℂ[X]) =
      Polynomial.C 1 + Polynomial.C (2 * a) * X + Polynomial.C (a ^ 2 + 2 * b) * X ^ 2 +
        Polynomial.C (2 + 2 * a * b) * X ^ 3 + Polynomial.C (b ^ 2 + 2 * a) * X ^ 4 +
          Polynomial.C (2 * b) * X ^ 5 + Polynomial.C 1 * X ^ 6 := by
    simp only [map_add, map_mul, map_pow, map_ofNat, map_one]
    ring
  rw [e]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C] <;> norm_num

/-- **The count of the zero-flux states at the ends**, for a finite subgroup of `SU(3)` with two
slots at each end: the coefficient of `z^k` in `⟨χ P⟩ ⟨χ̄ P⟩`, `P = det(1 + z g)²`, as a sum over
`i + j = k` of the coefficients `α_i` and `β_j`. -/
theorem screen_count [Fintype G] (hSU : ∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2))) (k : ℕ) :
    (Module.finrank ℂ ↥(sectorVec (Fin 2) k ⊓
        Fock.fixedSub (endMatter ρ (Edge.conjTriplet ρ) ρ ord)) : ℂ) =
      ∑ p ∈ Finset.antidiagonal k,
        ((Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace *
          ((1 + Polynomial.C (ρ g).trace * X + Polynomial.C (conj (ρ g).trace) * X ^ 2 +
            X ^ 3) ^ 2 : ℂ[X]).coeff p.1) *
        ((Fintype.card G : ℂ)⁻¹ * ∑ g, conj (ρ g).trace *
          ((1 + Polynomial.C (ρ g).trace * X + Polynomial.C (conj (ρ g).trace) * X ^ 2 +
            X ^ 3) ^ 2 : ℂ[X]).coeff p.2) := by
  rw [Fock.finrank_inf_fixedSub (endMatter ρ (Edge.conjTriplet ρ) ρ ord)
    (fun y => y.2.card = k) (sectorVec (Fin 2) k) (fun v => Iff.rfl)
    (fun h y y' hne => endMatter_respects ρ (Edge.conjTriplet ρ) ρ ord k h y y' hne)]
  simp only [sum_endMatter, trace_conjTriplet, Fintype.card_fin]
  have hP : ∀ g, (1 + (X : ℂ[X]) • (ρ g).map Polynomial.C).det ^ 2 =
      (1 + Polynomial.C (ρ g).trace * X + Polynomial.C (conj (ρ g).trace) * X ^ 2 + X ^ 3) ^ 2 :=
    fun g => by rw [Edge.det_one_add_X_smul_of_mem_specialUnitaryGroup (hSU g)]
  simp only [hP]
  rw [average_pairs (fun g => (ρ g).trace) (fun g => conj (ρ g).trace)
    (fun g => (1 + Polynomial.C (ρ g).trace * X + Polynomial.C (conj (ρ g).trace) * X ^ 2 +
      X ^ 3) ^ 2) k, Polynomial.coeff_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Polynomial.coeff_smul, Polynomial.coeff_smul, Polynomial.finsetSum_coeff,
    Polynomial.finsetSum_coeff, smul_eq_mul, smul_eq_mul]
  simp only [Polynomial.coeff_C_mul]

/-- The counts with `0` to `3` dynamical quarks, from the averages `⟨χ⟩ = 0` and `⟨χ χ̄⟩ = 1`:
none with `0` or `1` quark, `4 ⟨χ²⟩` with two, and `2 (⟨χ³⟩ + 2)` with three when `⟨χ²⟩ = 0`. -/
theorem screen_counts [Fintype G] (hSU : ∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2)))
    (m1 : (Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace = 0)
    (m11 : (Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace * conj (ρ g).trace = 1) :
    let F : ℕ → ℂ := fun k => (Module.finrank ℂ ↥(sectorVec (Fin 2) k ⊓
        Fock.fixedSub (endMatter ρ (Edge.conjTriplet ρ) ρ ord)) : ℂ)
    F 0 = 0 ∧ F 1 = 0 ∧ F 2 = 4 * ((Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace ^ 2) ∧
      ((Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace ^ 2 = 0 →
        F 3 = 2 * ((Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace ^ 3 + 2)) := by
  intro F
  set α : ℕ → ℂ := fun i => (Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace *
    ((1 + Polynomial.C (ρ g).trace * X + Polynomial.C (conj (ρ g).trace) * X ^ 2 +
      X ^ 3) ^ 2 : ℂ[X]).coeff i with hα
  set β : ℕ → ℂ := fun i => (Fintype.card G : ℂ)⁻¹ * ∑ g, conj (ρ g).trace *
    ((1 + Polynomial.C (ρ g).trace * X + Polynomial.C (conj (ρ g).trace) * X ^ 2 +
      X ^ 3) ^ 2 : ℂ[X]).coeff i with hβ
  have hF : ∀ k, F k = ∑ p ∈ Finset.antidiagonal k, α p.1 * β p.2 :=
    fun k => screen_count hSU ord k
  have a0 : α 0 = 0 := by
    rw [hα]
    simp only [(coeff_cubic_sq _ _).1, mul_one]
    exact m1
  have b0 : β 0 = 0 := by
    rw [hβ]
    simp only [(coeff_cubic_sq _ _).1, mul_one]
    have hsum : ∑ g, (ρ g).trace = 0 := by
      have hc : (Fintype.card G : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
      exact (mul_eq_zero.mp m1).resolve_left hc
    rw [← map_sum, hsum, map_zero, mul_zero]
  have a1 : α 1 = 2 * ((Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace ^ 2) := by
    rw [hα]
    simp only [(coeff_cubic_sq _ _).2.1]
    rw [show ∑ g, (ρ g).trace * (2 * (ρ g).trace) = 2 * ∑ g, (ρ g).trace ^ 2 by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ => by ring]
    ring
  have b1 : β 1 = 2 := by
    rw [hβ]
    simp only [(coeff_cubic_sq _ _).2.1]
    rw [show ∑ g, conj (ρ g).trace * (2 * (ρ g).trace) =
        2 * ∑ g, (ρ g).trace * conj (ρ g).trace by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ => by ring, mul_left_comm, m11, mul_one]
  have a2 : α 2 = (Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace ^ 3 + 2 := by
    rw [hα]
    simp only [(coeff_cubic_sq _ _).2.2]
    rw [show ∑ g, (ρ g).trace * ((ρ g).trace ^ 2 + 2 * conj (ρ g).trace) =
        ∑ g, (ρ g).trace ^ 3 + 2 * ∑ g, (ρ g).trace * conj (ρ g).trace by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun g _ => by ring, mul_add, mul_left_comm, m11, mul_one]
  refine ⟨?_, ?_, ?_, fun h2 => ?_⟩
  · rw [hF]
    simp [a0]
  · rw [hF, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [Finset.sum_range_succ, a0, b0]
  · rw [hF, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.sub_zero, Nat.sub_self, a0, b0, a1, b1, zero_mul, mul_zero, add_zero]
    ring
  · rw [hF, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.sub_zero, Nat.sub_self, a0, b0, a1, a2, b1, h2, zero_mul, mul_zero, add_zero]
    ring

end Counting

/-! ### Creations on the vacuum -/

section Creations

variable {M : Type*} [Fintype M] [DecidableEq M]

theorem creation_vac (ord : LinearOrder M) (m : M) :
    Fock.creation ord m *ᵥ Fock.ket ∅ = Fock.ket {m} := by
  rw [Fock.creation_mulVec_ket_of_notMem (Finset.notMem_empty m)]
  simp [Fock.precCount]

/-- `Γ(W) a†_{m₁} a†_{m₂} |0⟩ = (W a†)_{m₁} (W a†)_{m₂} |0⟩`. -/
theorem sq_cc (ord : LinearOrder M) (W : Matrix M M ℂ) (m₁ m₂ : M) :
    Fock.secondQuant ord W *ᵥ ((Fock.creation ord m₁ * Fock.creation ord m₂) *ᵥ Fock.ket ∅) =
      (Fock.transformedCreation ord W m₁ * Fock.transformedCreation ord W m₂) *ᵥ
        Fock.ket ∅ := by
  rw [Matrix.mulVec_mulVec, ← mul_assoc, Fock.secondQuant_mul_creation, mul_assoc,
    Fock.secondQuant_mul_creation, ← mul_assoc, ← Matrix.mulVec_mulVec,
    Fock.secondQuant_mulVec_vacuum]

/-- `Γ(W) a†_{m₁} a†_{m₂} a†_{m₃} |0⟩ = (W a†)_{m₁} (W a†)_{m₂} (W a†)_{m₃} |0⟩`. -/
theorem sq_ccc (ord : LinearOrder M) (W : Matrix M M ℂ) (m₁ m₂ m₃ : M) :
    Fock.secondQuant ord W *ᵥ ((Fock.creation ord m₁ * Fock.creation ord m₂ *
        Fock.creation ord m₃) *ᵥ Fock.ket ∅) =
      (Fock.transformedCreation ord W m₁ * Fock.transformedCreation ord W m₂ *
        Fock.transformedCreation ord W m₃) *ᵥ Fock.ket ∅ := by
  have key : Fock.secondQuant ord W * (Fock.creation ord m₁ * Fock.creation ord m₂ *
      Fock.creation ord m₃) = Fock.transformedCreation ord W m₁ *
        Fock.transformedCreation ord W m₂ * Fock.transformedCreation ord W m₃ *
          Fock.secondQuant ord W := by
    calc Fock.secondQuant ord W * (Fock.creation ord m₁ * Fock.creation ord m₂ *
          Fock.creation ord m₃) =
        Fock.secondQuant ord W * Fock.creation ord m₁ * Fock.creation ord m₂ *
          Fock.creation ord m₃ := by simp only [mul_assoc]
      _ = Fock.transformedCreation ord W m₁ * (Fock.secondQuant ord W * Fock.creation ord m₂) *
          Fock.creation ord m₃ := by rw [Fock.secondQuant_mul_creation]; simp only [mul_assoc]
      _ = Fock.transformedCreation ord W m₁ * Fock.transformedCreation ord W m₂ *
          (Fock.secondQuant ord W * Fock.creation ord m₃) := by
        rw [Fock.secondQuant_mul_creation]; simp only [mul_assoc]
      _ = _ := by rw [Fock.secondQuant_mul_creation]; simp only [mul_assoc]
  rw [Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec, Fock.secondQuant_mulVec_vacuum]

end Creations

section Transformed

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The transformed creation of a quark at `x` under `diag(g₀, g_R) ⊗ 1`. -/
theorem tc_inl (ord : LinearOrder (Edge.Mode (Fin 3) S)) (g₀ gR : Matrix (Fin 3) (Fin 3) ℂ)
    (c : Fin 3) (s : S) :
    Fock.transformedCreation ord (Edge.diag g₀ gR) (Sum.inl (c, s)) =
      ∑ p, g₀ p c • Fock.creation ord (Sum.inl (p, s)) := by
  rw [Fock.transformedCreation, Fintype.sum_sum_type]
  simp only [Edge.diag, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
    zero_smul, Finset.sum_const_zero, add_zero, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single s]
  · simp
  · intro s' _ hs'
    simp [hs']
  · simp

/-- The transformed creation of a quark at `y` under `diag(g₀, g_R) ⊗ 1`. -/
theorem tc_inr (ord : LinearOrder (Edge.Mode (Fin 3) S)) (g₀ gR : Matrix (Fin 3) (Fin 3) ℂ)
    (c : Fin 3) (s : S) :
    Fock.transformedCreation ord (Edge.diag g₀ gR) (Sum.inr (c, s)) =
      ∑ q, gR q c • Fock.creation ord (Sum.inr (q, s)) := by
  rw [Fock.transformedCreation, Fintype.sum_sum_type]
  simp only [Edge.diag, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
    zero_smul, Finset.sum_const_zero, zero_add, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_eq_single s]
  · simp
  · intro s' _ hs'
    simp [hs']
  · simp

/-- The matter of the string model applied to a vector. -/
theorem endMatter_mulVec (σ₀ σR : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (ord : LinearOrder (Edge.Mode (Fin 3) S)) (h : G × G)
    (v : (Fin 3 × Fin 3) × Finset (Edge.Mode (Fin 3) S) → ℂ) (x' : Fin 3 × Fin 3)
    (n' : Finset (Edge.Mode (Fin 3) S)) :
    (endMatter σ₀ σR ρ ord h *ᵥ v) (x', n') =
      ∑ x : Fin 3 × Fin 3, σ₀ h.1 x'.1 x.1 * σR h.2 x'.2 x.2 *
        (Edge.pairHom ρ ord h *ᵥ fun n => v (x, n)) n' := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, endMatter_apply, Finset.mul_sum,
    mul_assoc]

end Transformed

/-! ### The screened states are colourless -/

section Screened

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem sum_conj_mul (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ) (g : G) (a q : Fin 3) :
    ∑ x, Edge.conjTriplet ρ g a x * ρ g q x = if q = a then 1 else 0 := by
  have h := congrFun (congrFun (show ρ g * (Edge.conjTriplet ρ g)ᵀ = 1 by
    rw [conjTriplet_transpose hunit, ← map_mul, mul_inv_cancel, map_one]) q) a
  rw [Matrix.mul_apply] at h
  rw [show (∑ x, Edge.conjTriplet ρ g a x * ρ g q x) = ∑ x, ρ g q x * (Edge.conjTriplet ρ g)ᵀ x a
    from Finset.sum_congr rfl fun x _ => by rw [Matrix.transpose_apply, mul_comm], h,
    Matrix.one_apply]

theorem sum_real_mul (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hreal : ∀ g i j, conj (ρ g i j) = ρ g i j) (g : G) (a p : Fin 3) :
    ∑ x, ρ g a x * ρ g p x = if a = p then 1 else 0 := by
  have h := congrFun (congrFun (show ρ g * (ρ g)ᵀ = 1 by
    rw [transpose_of_real hunit hreal, ← map_mul, mul_inv_cancel, map_one]) a) p
  rw [Matrix.mul_apply] at h
  rw [show (∑ x, ρ g a x * ρ g p x) = ∑ x, ρ g a x * (ρ g)ᵀ x p from rfl, h, Matrix.one_apply]

omit [Group G] in
theorem sum4_comm (f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

omit [Group G] in
/-- `Σ_p Σ_q δ_{a p} δ_{q b} w(p, q) = w(a, b)`. -/
theorem sum_delta2 (a b : Fin 3) (w : Fin 3 → Fin 3 → ℂ) :
    ∑ p, ∑ q, (if a = p then 1 else 0) * (if q = b then 1 else 0) * w p q = w a b := by
  rw [Finset.sum_eq_single a (fun p _ hp => Finset.sum_eq_zero fun q _ => by
      rw [ite_eq_right (Ne.symm hp)]; ring) (by simp),
    Finset.sum_eq_single b (fun q _ hq => by rw [ite_eq_right hq]; ring) (by simp)]
  simp

/-- **One quark at each source is colourless** for a real triplet. -/
theorem pairScreen_fixed (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hreal : ∀ g i j, conj (ρ g i j) = ρ g i j) (ord : LinearOrder (Edge.Mode (Fin 3) S))
    (s t : S) (h : G × G) :
    endMatter ρ (Edge.conjTriplet ρ) ρ ord h *ᵥ pairScreen ord s t = pairScreen ord s t := by
  set w : Fin 3 → Fin 3 → Finset (Edge.Mode (Fin 3) S) → ℂ := fun p q =>
    (Fock.creation ord (Sum.inl (p, s)) * Fock.creation ord (Sum.inr (q, t))) *ᵥ Fock.ket ∅
    with hw
  have hin : ∀ x : Fin 3 × Fin 3, (Edge.pairHom ρ ord h *ᵥ fun n => pairScreen ord s t (x, n)) =
      ∑ p, ∑ q, (ρ h.1 p x.1 * ρ h.2 q x.2) • w p q := by
    intro x
    change Fock.secondQuant ord (Edge.diag (ρ h.1) (ρ h.2)) *ᵥ
      ((Fock.creation ord (Sum.inl (x.1, s)) * Fock.creation ord (Sum.inr (x.2, t))) *ᵥ
        Fock.ket ∅) = _
    rw [sq_cc, tc_inl, tc_inr, Finset.sum_mul_sum, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_mul_smul_comm, Matrix.smul_mulVec]
  funext y
  obtain ⟨x', n'⟩ := y
  rw [endMatter_mulVec]
  simp only [hin, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  simp only [← mul_assoc]
  have hcoef : ∀ p q, ∑ x1, ∑ x2, ρ h.1 x'.1 x1 * Edge.conjTriplet ρ h.2 x'.2 x2 *
      ρ h.1 p x1 * ρ h.2 q x2 * w p q n' =
      (if x'.1 = p then 1 else 0) * (if q = x'.2 then 1 else 0) * w p q n' := by
    intro p q
    rw [← sum_real_mul hunit hreal h.1 x'.1 p, ← sum_conj_mul hunit h.2 x'.2 q,
      Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x1 _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x2 _ => ?_
    ring
  rw [sum4_comm (fun x1 x2 p q => ρ h.1 x'.1 x1 * Edge.conjTriplet ρ h.2 x'.2 x2 * ρ h.1 p x1 *
    ρ h.2 q x2 * w p q n')]
  simp only [hcoef]
  exact sum_delta2 x'.1 x'.2 (fun p q => w p q n')

omit [Group G] in
theorem sum3_comm_single {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (f : ι → Fin 3 → Fin 3 → Fin 3 → M) :
    ∑ x, ∑ p, ∑ q, ∑ r, f x p q r = ∑ p, ∑ q, ∑ r, ∑ x, f x p q r := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact Finset.sum_comm

/-- The colour tensor of the screened state transforms back into itself:
`Σ_{x₁ a b} g_{x'₁ x₁} g_{p a} g_{q b} ε_{x₁ a b} Σ_{x₂} conj(h_{x'₂ x₂}) h_{r x₂}` is
`ε_{x'₁ p q} δ_{r x'₂}` for `g` of determinant one and `h` unitary. -/
theorem baryon_tensor (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hdet : ∀ g, (ρ g).det = 1) (h : G × G) (x' : Fin 3 × Fin 3) (p q r : Fin 3) :
    ∑ x : Fin 3 × Fin 3, ρ h.1 x'.1 x.1 * Edge.conjTriplet ρ h.2 x'.2 x.2 *
        (∑ a, ∑ b, leviCivita x.1 a b * (ρ h.1 p a * ρ h.1 q b * ρ h.2 r x.2)) =
      leviCivita x'.1 p q * (if r = x'.2 then 1 else 0) := by
  rw [← sum_conj_mul hunit h.2 x'.2 r]
  have ht := congrFun (congrFun (congrFun (Moments.t3_leviCivita (ρ h.1)) x'.1) p) q
  simp only [Moments.t3, Pi.smul_apply, smul_eq_mul, hdet, one_mul] at ht
  rw [← ht, Finset.sum_mul, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x1 _ => ?_
  simp only [Fin.sum_univ_three]
  ring

omit [Group G] in
theorem sum5_comm {M : Type*} [AddCommMonoid M] (f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → M) :
    ∑ a, ∑ b, ∑ p, ∑ q, ∑ r, f a b p q r = ∑ p, ∑ q, ∑ r, ∑ a, ∑ b, f a b p q r := by
  rw [Finset.sum_congr rfl fun a _ => sum3_comm_single (f a)]
  exact sum3_comm_single (fun a p q r => ∑ b, f a b p q r)

/-- **The antisymmetric colour pair at the quark source and a quark at the antiquark source are
colourless** for a triplet in `SU(3)`. -/
theorem baryonScreen_fixed (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hdet : ∀ g, (ρ g).det = 1) (ord : LinearOrder (Edge.Mode (Fin 3) S)) (s t u : S)
    (h : G × G) :
    endMatter ρ (Edge.conjTriplet ρ) ρ ord h *ᵥ baryonScreen ord s t u =
      baryonScreen ord s t u := by
  set w : Fin 3 → Fin 3 → Fin 3 → Finset (Edge.Mode (Fin 3) S) → ℂ := fun p q r =>
    (Fock.creation ord (Sum.inl (p, s)) * Fock.creation ord (Sum.inl (q, t)) *
      Fock.creation ord (Sum.inr (r, u))) *ᵥ Fock.ket ∅ with hw
  have hv : ∀ x : Fin 3 × Fin 3, (fun n => baryonScreen ord s t u (x, n)) =
      ∑ a, ∑ b, leviCivita x.1 a b • w a b x.2 := by
    intro x
    funext n
    simp only [baryonScreen, Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply,
      Pi.smul_apply, hw]
  have hsq : ∀ a b c, Edge.pairHom ρ ord h *ᵥ w a b c =
      ∑ p, ∑ q, ∑ r, (ρ h.1 p a * ρ h.1 q b * ρ h.2 r c) • w p q r := by
    intro a b c
    change Fock.secondQuant ord (Edge.diag (ρ h.1) (ρ h.2)) *ᵥ
      ((Fock.creation ord (Sum.inl (a, s)) * Fock.creation ord (Sum.inl (b, t)) *
        Fock.creation ord (Sum.inr (c, u))) *ᵥ Fock.ket ∅) = _
    rw [sq_ccc, tc_inl, tc_inl, tc_inr, Finset.sum_mul_sum, Finset.sum_mul, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [smul_mul_smul_comm, smul_mul_smul_comm, Matrix.smul_mulVec]
  have hsqb : ∀ x : Fin 3 × Fin 3,
      (Edge.pairHom ρ ord h *ᵥ fun n => baryonScreen ord s t u (x, n)) =
      ∑ p, ∑ q, ∑ r, (∑ a, ∑ b, leviCivita x.1 a b * (ρ h.1 p a * ρ h.1 q b * ρ h.2 r x.2)) •
        w p q r := by
    intro x
    rw [hv x, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, hsq, Finset.smul_sum, smul_smul]
    rw [sum5_comm]
    simp only [Finset.sum_smul]
  funext y
  obtain ⟨x', n'⟩ := y
  rw [endMatter_mulVec]
  simp only [hsqb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [sum3_comm_single]
  have hcoef : ∀ p q r, ∑ x : Fin 3 × Fin 3, ρ h.1 x'.1 x.1 * Edge.conjTriplet ρ h.2 x'.2 x.2 *
      ((∑ a, ∑ b, leviCivita x.1 a b * (ρ h.1 p a * ρ h.1 q b * ρ h.2 r x.2)) * w p q r n') =
      leviCivita x'.1 p q * (if r = x'.2 then 1 else 0) * w p q r n' := by
    intro p q r
    rw [← baryon_tensor hunit hdet h x' p q r, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  simp only [hcoef, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  change _ = ((∑ a, ∑ b, leviCivita x'.1 a b • (Fock.creation ord (Sum.inl (a, s)) *
    Fock.creation ord (Sum.inl (b, t)) * Fock.creation ord (Sum.inr (x'.2, u)))) *ᵥ
    Fock.ket ∅) n'
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, hw]

end Screened

/-! ### The screened vectors: values, sectors and independence -/

section Values

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- Two creations on the vacuum give a multiple of the ket of the two modes, a nonzero one exactly
when the modes differ. -/
theorem cc_vac (ord : LinearOrder M) (m₁ m₂ : M) :
    ∃ e : ℂ, (Fock.creation ord m₁ * Fock.creation ord m₂) *ᵥ Fock.ket ∅ =
      e • Fock.ket {m₁, m₂} ∧ (e ≠ 0 ↔ m₁ ≠ m₂) := by
  rw [← Matrix.mulVec_mulVec, creation_vac]
  by_cases h : m₁ ∈ ({m₂} : Finset M)
  · exact ⟨0, by rw [Fock.creation_mulVec_ket_of_mem h, zero_smul],
      iff_of_false (fun h0 => h0 rfl) fun hne => hne (Finset.mem_singleton.mp h)⟩
  · exact ⟨_, Fock.creation_mulVec_ket_of_notMem h,
      iff_of_true (pow_ne_zero _ (by norm_num)) fun e => h (Finset.mem_singleton.mpr e)⟩

/-- Three creations on the vacuum give a multiple of the ket of the three modes, a nonzero one
exactly when the modes are different. -/
theorem ccc_vac (ord : LinearOrder M) (m₁ m₂ m₃ : M) :
    ∃ e : ℂ, (Fock.creation ord m₁ * Fock.creation ord m₂ * Fock.creation ord m₃) *ᵥ
        Fock.ket ∅ = e • Fock.ket {m₁, m₂, m₃} ∧
      (e ≠ 0 ↔ m₁ ≠ m₂ ∧ m₁ ≠ m₃ ∧ m₂ ≠ m₃) := by
  obtain ⟨e, he, hne⟩ := cc_vac ord m₂ m₃
  rw [mul_assoc, ← Matrix.mulVec_mulVec, he, Matrix.mulVec_smul]
  by_cases h : m₁ ∈ ({m₂, m₃} : Finset M)
  · refine ⟨0, by rw [Fock.creation_mulVec_ket_of_mem h, smul_zero, zero_smul],
      iff_of_false (fun h0 => h0 rfl) ?_⟩
    rintro ⟨h12, h13, -⟩
    rcases Finset.mem_insert.mp h with h' | h'
    · exact h12 h'
    · exact h13 (Finset.mem_singleton.mp h')
  · refine ⟨e * (-1) ^ Fock.precCount ord {m₂, m₃} m₁, ?_, ?_⟩
    · rw [Fock.creation_mulVec_ket_of_notMem h, smul_smul]
    · have h12 : m₁ ≠ m₂ := fun e => h (by simp [e])
      have h13 : m₁ ≠ m₃ := fun e => h (by simp [e])
      rw [ne_eq, mul_eq_zero, not_or, ← ne_eq, hne]
      exact ⟨fun hh => ⟨h12, h13, hh.1⟩, fun hh => ⟨hh.2.2, pow_ne_zero _ (by norm_num)⟩⟩

omit [Fintype M] in
theorem smul_ket_apply (e : ℂ) (N n : Finset M) :
    (e • Fock.ket N) n = if n = N then e else 0 := by
  simp [Fock.ket, Pi.single_apply]

end Values

omit [Group G] in
/-- A family of vectors is independent when each has a point where it alone is not zero. -/
theorem linearIndependent_of_points {ι β : Type*} (v : ι → β → ℂ) (p : ι → β)
    (hoff : ∀ i j, i ≠ j → v i (p j) = 0) (hdiag : ∀ i, v i (p i) ≠ 0) :
    LinearIndependent ℂ v := by
  classical
  rw [linearIndependent_iff']
  intro s c hc j hj
  have h := congrFun hc (p j)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [hoff i j hij, mul_zero])
    (fun h' => absurd hj h')] at h
  exact (mul_eq_zero.mp h).resolve_right (hdiag j)

/-- `ε_{cba} = -ε_{cab}`. -/
theorem leviCivita_swap (c a b : Fin 3) : leviCivita c b a = -leviCivita c a b := by
  have h : ∀ c a b : Fin 3, Moments.lcTab c b a = -Moments.lcTab c a b := by decide
  rw [Moments.leviCivita_eq, Moments.leviCivita_eq, h]
  push_cast
  ring

section Vectors

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- One quark at each source is the multiple `e ≠ 0` of the ket of its two modes. -/
theorem pairScreen_eq (ord : LinearOrder (Edge.Mode (Fin 3) S)) (s t : S) (x : Fin 3 × Fin 3) :
    ∃ e : ℂ, e ≠ 0 ∧ ∀ n, pairScreen ord s t (x, n) =
      if n = {Sum.inl (x.1, s), Sum.inr (x.2, t)} then e else 0 := by
  obtain ⟨e, he, hne⟩ := cc_vac ord (Sum.inl (x.1, s)) (Sum.inr (x.2, t))
  exact ⟨e, hne.mpr Sum.inl_ne_inr, fun n => by
    change ((Fock.creation ord _ * Fock.creation ord _) *ᵥ Fock.ket ∅) n = _
    rw [he, smul_ket_apply]⟩

theorem pairScreen_support (ord : LinearOrder (Edge.Mode (Fin 3) S)) (s t : S)
    (x : Fin 3 × Fin 3) (n : Finset (Edge.Mode (Fin 3) S)) (h : pairScreen ord s t (x, n) ≠ 0) :
    n = {Sum.inl (x.1, s), Sum.inr (x.2, t)} := by
  obtain ⟨e, -, he⟩ := pairScreen_eq ord s t x
  rw [he] at h
  by_contra hn
  exact h (ite_eq_right hn)

/-- One quark at each source has two dynamical quarks. -/
theorem pairScreen_mem_sector (ord : LinearOrder (Edge.Mode (Fin 3) S)) (s t : S) :
    pairScreen ord s t ∈ sectorVec S 2 := by
  rintro ⟨x, n⟩ h
  rw [pairScreen_support ord s t x n h]
  exact Finset.card_pair Sum.inl_ne_inr

/-- One quark at each source has one quark at each end. -/
theorem constState_pairScreen_mem (ord : LinearOrder (Edge.Mode (Fin 3) S)) (s t : S) :
    constState R (G := G) (pairScreen ord s t) ∈ endSector (C := Fin 3) R 1 1 := by
  rintro U ⟨x, n⟩ h
  rw [pairScreen_support ord s t x n h]
  refine ⟨?_, ?_⟩
  · rw [show (({Sum.inl (x.1, s), Sum.inr (x.2, t)} : Finset (Edge.Mode (Fin 3) S))).toLeft =
      {(x.1, s)} by ext y; simp]
    rfl
  · rw [show (({Sum.inl (x.1, s), Sum.inr (x.2, t)} : Finset (Edge.Mode (Fin 3) S))).toRight =
      {(x.2, t)} by ext y; simp]
    rfl

theorem baryonScreen_apply (ord : LinearOrder (Edge.Mode (Fin 3) S)) (s t u : S)
    (x : Fin 3 × Fin 3) (n : Finset (Edge.Mode (Fin 3) S)) :
    baryonScreen ord s t u (x, n) = ∑ a, ∑ b, leviCivita x.1 a b *
      ((Fock.creation ord (Sum.inl (a, s)) * Fock.creation ord (Sum.inl (b, t)) *
        Fock.creation ord (Sum.inr (x.2, u))) *ᵥ Fock.ket ∅) n := by
  simp only [baryonScreen, Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

/-- Where the antisymmetric pair is not zero: on the three modes of one of its terms. -/
theorem baryonScreen_support (ord : LinearOrder (Edge.Mode (Fin 3) S)) (s t u : S)
    (x : Fin 3 × Fin 3) (n : Finset (Edge.Mode (Fin 3) S))
    (h : baryonScreen ord s t u (x, n) ≠ 0) :
    ∃ a b : Fin 3, n = {Sum.inl (a, s), Sum.inl (b, t), Sum.inr (x.2, u)} ∧ (a, s) ≠ (b, t) := by
  rw [baryonScreen_apply] at h
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  obtain ⟨e, he, hne⟩ := ccc_vac ord (Sum.inl (a, s)) (Sum.inl (b, t)) (Sum.inr (x.2, u))
  rw [he, smul_ket_apply] at hb
  by_cases hn : n = {Sum.inl (a, s), Sum.inl (b, t), Sum.inr (x.2, u)}
  · rw [ite_eq_left hn] at hb
    exact ⟨a, b, hn, fun hab => (hne.mp (right_ne_zero_of_mul hb)).1 (by rw [hab])⟩
  · rw [ite_eq_right hn, mul_zero] at hb
    exact absurd rfl hb

/-- The antisymmetric pair with a quark at the antiquark source has three dynamical quarks. -/
theorem baryonScreen_mem_sector (ord : LinearOrder (Edge.Mode (Fin 3) S)) (s t u : S) :
    baryonScreen ord s t u ∈ sectorVec S 3 := by
  rintro ⟨x, n⟩ h
  obtain ⟨a, b, rfl, hab⟩ := baryonScreen_support ord s t u x n h
  exact Finset.card_eq_three.mpr ⟨_, _, _, fun e => hab (Sum.inl_injective e), Sum.inl_ne_inr,
    Sum.inl_ne_inr, rfl⟩

/-- The antisymmetric pair with a quark at the antiquark source has two quarks at the quark
source and one at the antiquark source. -/
theorem constState_baryonScreen_mem (ord : LinearOrder (Edge.Mode (Fin 3) S)) (s t u : S) :
    constState R (G := G) (baryonScreen ord s t u) ∈ endSector (C := Fin 3) R 2 1 := by
  rintro U ⟨x, n⟩ h
  obtain ⟨a, b, rfl, hab⟩ := baryonScreen_support ord s t u x n h
  refine ⟨?_, ?_⟩
  · rw [show (({Sum.inl (a, s), Sum.inl (b, t), Sum.inr (x.2, u)} :
        Finset (Edge.Mode (Fin 3) S))).toLeft = {(a, s), (b, t)} by ext y; simp]
    exact Finset.card_pair hab
  · rw [show (({Sum.inl (a, s), Sum.inl (b, t), Sum.inr (x.2, u)} :
        Finset (Edge.Mode (Fin 3) S))).toRight = {(x.2, u)} by ext y; simp]
    rfl

/-- **The antisymmetric pair is symmetric in its two slots.** -/
theorem baryonScreen_symm (ord : LinearOrder (Edge.Mode (Fin 3) S)) (s t u : S) :
    baryonScreen ord s t u = baryonScreen ord t s u := by
  have key : ∀ c c', (∑ a, ∑ b, leviCivita c a b • (Fock.creation ord (Sum.inl (a, s)) *
      Fock.creation ord (Sum.inl (b, t)) * Fock.creation ord (Sum.inr (c', u)))) =
      ∑ a, ∑ b, leviCivita c a b • (Fock.creation ord (Sum.inl (a, t)) *
        Fock.creation ord (Sum.inl (b, s)) * Fock.creation ord (Sum.inr (c', u))) := by
    intro c c'
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [leviCivita_swap, Fock.creation_mul_creation ord (Sum.inl (b, s)) (Sum.inl (a, t)),
      neg_mul, neg_smul, smul_neg, neg_neg]
  funext x
  unfold baryonScreen
  rw [key]

/-- The coefficients of the antisymmetric pair at the source colour `0`. -/
theorem baryonScreen_zero (ord : LinearOrder (Edge.Mode (Fin 3) S)) (s t u : S) (c' : Fin 3)
    (n : Finset (Edge.Mode (Fin 3) S)) :
    baryonScreen ord s t u ((0, c'), n) =
      ((Fock.creation ord (Sum.inl (1, s)) * Fock.creation ord (Sum.inl (2, t)) *
        Fock.creation ord (Sum.inr (c', u))) *ᵥ Fock.ket ∅) n -
      ((Fock.creation ord (Sum.inl (2, s)) * Fock.creation ord (Sum.inl (1, t)) *
        Fock.creation ord (Sum.inr (c', u))) *ᵥ Fock.ket ∅) n := by
  rw [baryonScreen_apply]
  simp only [Fin.sum_univ_three, Moments.leviCivita_eq]
  simp [Moments.lcTab]
  ring

end Vectors

/-- The four vectors with one quark at each source are independent. -/
theorem pairScreen_independent (ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2))) :
    LinearIndependent ℂ (fun st : Fin 2 × Fin 2 => pairScreen ord st.1 st.2) := by
  have hpts : ∀ i j : Fin 2 × Fin 2,
      ({Sum.inl (0, j.1), Sum.inr (0, j.2)} : Finset (Edge.Mode (Fin 3) (Fin 2))) =
        {Sum.inl (0, i.1), Sum.inr (0, i.2)} → i = j := by decide
  refine linearIndependent_of_points _
    (fun st => ((0, 0), {Sum.inl (0, st.1), Sum.inr (0, st.2)})) (fun i j hij => ?_)
    (fun i => ?_)
  · obtain ⟨e, -, he⟩ := pairScreen_eq ord i.1 i.2 (0, 0)
    exact (he _).trans (ite_eq_right fun h => hij (hpts i j h))
  · obtain ⟨e, he0, he⟩ := pairScreen_eq ord i.1 i.2 (0, 0)
    exact ((he _).trans (ite_eq_left rfl)).trans_ne he0

/-- The test occupation table of the antisymmetric pair in the slots `s ≤ t` with a quark in the
slot `u` at the antiquark source. -/
def baryonPoint (p : {st : Fin 2 × Fin 2 // st.1 ≤ st.2} × Fin 2) :
    Finset (Edge.Mode (Fin 3) (Fin 2)) :=
  {Sum.inl (1, p.1.1.1), Sum.inl (2, p.1.1.2), Sum.inr (0, p.2)}

/-- The six vectors of the antisymmetric pair are independent. -/
theorem baryonScreen_independent (ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2))) :
    LinearIndependent ℂ (fun p : {st : Fin 2 × Fin 2 // st.1 ≤ st.2} × Fin 2 =>
      baryonScreen ord p.1.1.1 p.1.1.2 p.2) := by
  have hinj : ∀ i j : {st : Fin 2 × Fin 2 // st.1 ≤ st.2} × Fin 2,
      baryonPoint j = ({Sum.inl (1, i.1.1.1), Sum.inl (2, i.1.1.2), Sum.inr (0, i.2)} :
        Finset (Edge.Mode (Fin 3) (Fin 2))) → i = j := by decide
  have hswap : ∀ i j : {st : Fin 2 × Fin 2 // st.1 ≤ st.2} × Fin 2,
      baryonPoint j = ({Sum.inl (2, i.1.1.1), Sum.inl (1, i.1.1.2), Sum.inr (0, i.2)} :
        Finset (Edge.Mode (Fin 3) (Fin 2))) → i.1.1.1 = i.1.1.2 ∧ i = j := by decide
  refine linearIndependent_of_points _ (fun p => ((0, 0), baryonPoint p)) (fun i j hij => ?_)
    (fun i => ?_)
  · obtain ⟨e₁, he₁, -⟩ := ccc_vac ord (Sum.inl ((1 : Fin 3), i.1.1.1))
      (Sum.inl ((2 : Fin 3), i.1.1.2)) (Sum.inr ((0 : Fin 3), i.2))
    obtain ⟨e₂, he₂, -⟩ := ccc_vac ord (Sum.inl ((2 : Fin 3), i.1.1.1))
      (Sum.inl ((1 : Fin 3), i.1.1.2)) (Sum.inr ((0 : Fin 3), i.2))
    rw [baryonScreen_zero, he₁, he₂, smul_ket_apply, smul_ket_apply,
      ite_eq_right fun h => hij (hinj i j h), ite_eq_right fun h => hij (hswap i j h).2, sub_zero]
  · obtain ⟨⟨⟨s, t⟩, hst⟩, u⟩ := i
    change baryonScreen ord s t u ((0, 0), {Sum.inl (1, s), Sum.inl (2, t), Sum.inr (0, u)}) ≠ 0
    obtain ⟨e₁, he₁, hne₁⟩ := ccc_vac ord (Sum.inl ((1 : Fin 3), s))
      (Sum.inl ((2 : Fin 3), t)) (Sum.inr ((0 : Fin 3), u))
    have he₁0 : e₁ ≠ 0 := hne₁.mpr ⟨by simp, Sum.inl_ne_inr, Sum.inl_ne_inr⟩
    rw [baryonScreen_zero]
    by_cases hts : s = t
    · subst hts
      rw [Fock.creation_mul_creation ord (Sum.inl ((2 : Fin 3), s)) (Sum.inl ((1 : Fin 3), s)),
        neg_mul, Matrix.neg_mulVec, Pi.neg_apply, sub_neg_eq_add, he₁, smul_ket_apply,
        ite_eq_left rfl]
      exact fun h => he₁0 (by linear_combination h / 2)
    · obtain ⟨e₂, he₂, -⟩ := ccc_vac ord (Sum.inl ((2 : Fin 3), s))
        (Sum.inl ((1 : Fin 3), t)) (Sum.inr ((0 : Fin 3), u))
      have hne : ({Sum.inl (1, s), Sum.inl (2, t), Sum.inr (0, u)} :
          Finset (Edge.Mode (Fin 3) (Fin 2))) ≠ {Sum.inl (2, s), Sum.inl (1, t), Sum.inr (0, u)} :=
        fun h => hts (hswap ⟨⟨(s, t), hst⟩, u⟩ ⟨⟨(s, t), hst⟩, u⟩ h).1
      rw [he₁, he₂, smul_ket_apply, smul_ket_apply, ite_eq_left rfl, ite_eq_right hne, sub_zero]
      exact he₁0

/-! ### The zero-flux sectors (Proposition 13.3) -/

/-- The vectors of the matter at the ends with `k` dynamical quarks fixed by every gauge pair. -/
noncomputable def endFixed (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ)
    (ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2))) (k : ℕ) :
    Submodule ℂ ((Fin 3 × Fin 3) × Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ) :=
  sectorVec (Fin 2) k ⊓ Fock.fixedSub (endMatter ρ (Edge.conjTriplet ρ) ρ ord)

/-- The zero-flux states with `k` dynamical quarks are the constant states of the fixed vectors
with `k` quarks. -/
theorem zeroFlux_quark_eq (hR : 0 < R) (ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2))) (k : ℕ) :
    zeroFlux R (endMatter ρ (Edge.conjTriplet ρ) ρ ord) ⊓ quarkSector R k =
      (endFixed ρ ord k).map constLin := by
  rw [quarkSector_eq, zeroFlux_inf_eq hR]
  rfl

theorem finrank_zeroFlux_quark (hR : 0 < R) (ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2)))
    (k : ℕ) :
    Module.finrank ℂ ↥(zeroFlux R (endMatter ρ (Edge.conjTriplet ρ) ρ ord) ⊓ quarkSector R k) =
      Module.finrank ℂ ↥(endFixed ρ ord k) := by
  rw [zeroFlux_quark_eq hR]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ constLin_injective _)).symm

/-- **Proposition 13.3 for a real triplet**, from the counts of the fixed vectors. -/
theorem real_part (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hreal : ∀ g i j, conj (ρ g i j) = ρ g i j) (hR : 0 < R)
    {ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2))} (h0 : endFixed ρ ord 0 = ⊥)
    (h1 : endFixed ρ ord 1 = ⊥) (h2 : Module.finrank ℂ ↥(endFixed ρ ord 2) = 4) :
    (∀ k < 2, zeroFlux R (endMatter ρ (Edge.conjTriplet ρ) ρ ord) ⊓ quarkSector R k = ⊥) ∧
    zeroFlux R (endMatter ρ (Edge.conjTriplet ρ) ρ ord) ⊓ quarkSector R 2 =
      Submodule.span ℂ (Set.range fun st : Fin 2 × Fin 2 =>
        constState R (G := G) (pairScreen ord st.1 st.2)) ∧
    zeroFlux R (endMatter ρ (Edge.conjTriplet ρ) ρ ord) ⊓ quarkSector R 2 ≤ endSector R 1 1 ∧
    Module.finrank ℂ ↥(zeroFlux R (endMatter ρ (Edge.conjTriplet ρ) ρ ord) ⊓
      quarkSector R 2) = 4 := by
  have hspan : Submodule.span ℂ (Set.range fun st : Fin 2 × Fin 2 => pairScreen ord st.1 st.2) =
      endFixed ρ ord 2 := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨st, rfl⟩
      exact Submodule.mem_inf.mpr ⟨pairScreen_mem_sector ord st.1 st.2,
        pairScreen_fixed hunit hreal ord st.1 st.2⟩
    · rw [finrank_span_eq_card (pairScreen_independent ord), h2]
      simp
  have hZ2 : zeroFlux R (endMatter ρ (Edge.conjTriplet ρ) ρ ord) ⊓ quarkSector R 2 =
      Submodule.span ℂ (Set.range fun st : Fin 2 × Fin 2 =>
        constState R (G := G) (pairScreen ord st.1 st.2)) := by
    rw [zeroFlux_quark_eq hR, ← hspan, Submodule.map_span, ← Set.range_comp]
    rfl
  refine ⟨fun k hk => ?_, hZ2, ?_, (finrank_zeroFlux_quark hR ord 2).trans h2⟩
  · rw [zeroFlux_quark_eq hR]
    interval_cases k
    · rw [h0, Submodule.map_bot]
    · rw [h1, Submodule.map_bot]
  · rw [hZ2, Submodule.span_le]
    rintro _ ⟨st, rfl⟩
    exact constState_pairScreen_mem ord st.1 st.2

/-- **Proposition 13.3 for a complex triplet**, from the counts of the fixed vectors. -/
theorem complex_part (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hdet : ∀ g, (ρ g).det = 1) (hR : 0 < R) {ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2))}
    (h0 : endFixed ρ ord 0 = ⊥) (h1 : endFixed ρ ord 1 = ⊥) (h2 : endFixed ρ ord 2 = ⊥)
    (h3 : Module.finrank ℂ ↥(endFixed ρ ord 3) ≤ 6) :
    (∀ k < 3, zeroFlux R (endMatter ρ (Edge.conjTriplet ρ) ρ ord) ⊓ quarkSector R k = ⊥) ∧
    zeroFlux R (endMatter ρ (Edge.conjTriplet ρ) ρ ord) ⊓ quarkSector R 3 =
      Submodule.span ℂ (Set.range fun p : {st : Fin 2 × Fin 2 // st.1 ≤ st.2} × Fin 2 =>
        constState R (G := G) (baryonScreen ord p.1.1.1 p.1.1.2 p.2)) ∧
    (∀ s t u, baryonScreen ord s t u = baryonScreen ord t s u) ∧
    zeroFlux R (endMatter ρ (Edge.conjTriplet ρ) ρ ord) ⊓ quarkSector R 3 ≤ endSector R 2 1 ∧
    Module.finrank ℂ ↥(zeroFlux R (endMatter ρ (Edge.conjTriplet ρ) ρ ord) ⊓
      quarkSector R 3) = 6 := by
  have hle : Submodule.span ℂ (Set.range fun p : {st : Fin 2 × Fin 2 // st.1 ≤ st.2} × Fin 2 =>
      baryonScreen ord p.1.1.1 p.1.1.2 p.2) ≤ endFixed ρ ord 3 := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact Submodule.mem_inf.mpr ⟨baryonScreen_mem_sector ord _ _ _,
      baryonScreen_fixed hunit hdet ord _ _ _⟩
  have hcard : Module.finrank ℂ ↥(Submodule.span ℂ (Set.range
      fun p : {st : Fin 2 × Fin 2 // st.1 ≤ st.2} × Fin 2 =>
        baryonScreen ord p.1.1.1 p.1.1.2 p.2)) = 6 := by
    rw [finrank_span_eq_card (baryonScreen_independent ord)]
    decide
  have h3' : Module.finrank ℂ ↥(endFixed ρ ord 3) = 6 :=
    le_antisymm h3 (by rw [← hcard]; exact Submodule.finrank_mono hle)
  have hspan := Submodule.eq_of_le_of_finrank_eq hle (hcard.trans h3'.symm)
  have hZ3 : zeroFlux R (endMatter ρ (Edge.conjTriplet ρ) ρ ord) ⊓ quarkSector R 3 =
      Submodule.span ℂ (Set.range fun p : {st : Fin 2 × Fin 2 // st.1 ≤ st.2} × Fin 2 =>
        constState R (G := G) (baryonScreen ord p.1.1.1 p.1.1.2 p.2)) := by
    rw [zeroFlux_quark_eq hR, ← hspan, Submodule.map_span, ← Set.range_comp]
    rfl
  refine ⟨fun k hk => ?_, hZ3, baryonScreen_symm ord, ?_,
    (finrank_zeroFlux_quark hR ord 3).trans h3'⟩
  · rw [zeroFlux_quark_eq hR]
    interval_cases k
    · rw [h0, Submodule.map_bot]
    · rw [h1, Submodule.map_bot]
    · rw [h2, Submodule.map_bot]
  · rw [hZ3, Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact constState_baryonScreen_mem ord _ _ _

/-- **Proposition 13.3 for one colour group**, from the counts of the fixed vectors at the ends:
none with fewer than `2` quarks and four with `2` for a real triplet, none with fewer than `3`
quarks and at most six with `3` for a complex one. -/
theorem screening_of (hunit : ∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hdet : ∀ g, (ρ g).det = 1)
    (hr : (∀ g i j, conj (ρ g i j) = ρ g i j) → ∀ ord, endFixed ρ ord 0 = ⊥ ∧
      endFixed ρ ord 1 = ⊥ ∧ Module.finrank ℂ ↥(endFixed ρ ord 2) = 4)
    (hc : ¬ (∀ g i j, conj (ρ g i j) = ρ g i j) → ∀ ord, endFixed ρ ord 0 = ⊥ ∧
      endFixed ρ ord 1 = ⊥ ∧ endFixed ρ ord 2 = ⊥ ∧ Module.finrank ℂ ↥(endFixed ρ ord 3) ≤ 6) :
    ∀ (ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2))) (R : ℕ), 0 < R →
      let Z : ℕ → Submodule ℂ ((Canvas.path R).skeleton.LinkTable G →
          (Fin 3 × Fin 3) × Finset (Edge.Mode (Fin 3) (Fin 2)) → ℂ) := fun k =>
        zeroFlux R (endMatter ρ (Edge.conjTriplet ρ) ρ ord) ⊓ quarkSector R k
      ((∀ g i j, conj (ρ g i j) = ρ g i j) →
        (∀ k < 2, Z k = ⊥) ∧
        Z 2 = Submodule.span ℂ (Set.range fun st : Fin 2 × Fin 2 =>
          constState R (G := G) (pairScreen ord st.1 st.2)) ∧
        Z 2 ≤ endSector R 1 1 ∧
        Module.finrank ℂ ↥(Z 2) = 4) ∧
      (¬ (∀ g i j, conj (ρ g i j) = ρ g i j) →
        (∀ k < 3, Z k = ⊥) ∧
        Z 3 = Submodule.span ℂ (Set.range fun p : {st : Fin 2 × Fin 2 // st.1 ≤ st.2} × Fin 2 =>
          constState R (G := G) (baryonScreen ord p.1.1.1 p.1.1.2 p.2)) ∧
        (∀ s t u, baryonScreen ord s t u = baryonScreen ord t s u) ∧
        Z 3 ≤ endSector R 2 1 ∧
        Module.finrank ℂ ↥(Z 3) = 6) := by
  intro ord R hR Z
  refine ⟨fun hreal => ?_, fun hnr => ?_⟩
  · obtain ⟨h0, h1, h2⟩ := hr hreal ord
    exact real_part hunit hreal hR h0 h1 h2
  · obtain ⟨h0, h1, h2, h3⟩ := hc hnr ord
    exact complex_part hunit hdet hR h0 h1 h2 h3

/-! ### The counts of the fixed vectors at the ends -/

omit [Group G] in
theorem avg_eq [Fintype G] (f : G → ℂ) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g, f g = groupAvg G f := by
  rw [groupAvg, Nat.card_eq_fintype_card, finsum_eq_sum_of_fintype]

theorem trace_conj_of_real (hreal : ∀ g i j, conj (ρ g i j) = ρ g i j) (g : G) :
    conj (ρ g).trace = (ρ g).trace := by
  simp only [Matrix.trace, Matrix.diag, map_sum, hreal]

theorem endFixed_eq_bot {ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2))} {k : ℕ}
    (h : (Module.finrank ℂ ↥(endFixed ρ ord k) : ℂ) = 0) : endFixed ρ ord k = ⊥ :=
  Submodule.finrank_eq_zero.mp (by exact_mod_cast h)

/-- The counts for a real triplet of a finite subgroup of `SU(3)` with `⟨χ⟩ = 0` and
`⟨χ²⟩ = 1`. -/
theorem real_counts [Finite G] (hSU : ∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (hreal : ∀ g i j, conj (ρ g i j) = ρ g i j)
    (m1 : groupAvg G (fun g => (ρ g).trace) = 0)
    (m2 : groupAvg G (fun g => (ρ g).trace ^ 2) = 1)
    (ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2))) :
    endFixed ρ ord 0 = ⊥ ∧ endFixed ρ ord 1 = ⊥ ∧ Module.finrank ℂ ↥(endFixed ρ ord 2) = 4 := by
  have := Fintype.ofFinite G
  have m1' : (Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace = 0 := by rw [avg_eq]; exact m1
  have m2' : (Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace ^ 2 = 1 := by rw [avg_eq]; exact m2
  have m11 : (Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace * conj (ρ g).trace = 1 := by
    rw [← m2']
    congr 1
    exact Finset.sum_congr rfl fun g _ => by rw [trace_conj_of_real hreal, sq]
  have hc := screen_counts hSU ord m1' m11
  dsimp only at hc
  obtain ⟨f0, f1, f2, -⟩ := hc
  rw [m2', mul_one] at f2
  exact ⟨endFixed_eq_bot f0, endFixed_eq_bot f1, by exact_mod_cast f2⟩

/-- The counts for a complex triplet of a finite subgroup of `SU(3)` with `⟨χ⟩ = 0`,
`⟨χ χ̄⟩ = 1`, `⟨χ²⟩ = 0` and `⟨χ³⟩ = 1`. -/
theorem complex_counts [Finite G] (hSU : ∀ g, ρ g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (m1 : groupAvg G (fun g => (ρ g).trace) = 0)
    (m11 : groupAvg G (fun g => (ρ g).trace * conj (ρ g).trace) = 1)
    (m2 : groupAvg G (fun g => (ρ g).trace ^ 2) = 0)
    (m3 : groupAvg G (fun g => (ρ g).trace ^ 3) = 1)
    (ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2))) :
    endFixed ρ ord 0 = ⊥ ∧ endFixed ρ ord 1 = ⊥ ∧ endFixed ρ ord 2 = ⊥ ∧
      Module.finrank ℂ ↥(endFixed ρ ord 3) = 6 := by
  have := Fintype.ofFinite G
  have m1' : (Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace = 0 := by rw [avg_eq]; exact m1
  have m11' : (Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace * conj (ρ g).trace = 1 := by
    rw [avg_eq]; exact m11
  have m2' : (Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace ^ 2 = 0 := by rw [avg_eq]; exact m2
  have m3' : (Fintype.card G : ℂ)⁻¹ * ∑ g, (ρ g).trace ^ 3 = 1 := by rw [avg_eq]; exact m3
  have hc := screen_counts hSU ord m1' m11'
  dsimp only at hc
  obtain ⟨f0, f1, f2, f3⟩ := hc
  rw [m2', mul_zero] at f2
  have f3' := f3 m2'
  rw [m3'] at f3'
  norm_num at f3'
  exact ⟨endFixed_eq_bot f0, endFixed_eq_bot f1, endFixed_eq_bot f2, by exact_mod_cast f3'⟩

/-! ### The moments `⟨χ⟩`, `⟨χ χ̄⟩` and `⟨χ³⟩` of the four finite groups -/

theorem cube_sum : ∑ k : Fin 24, Exact.M3Z.trace (cubeE k) = ⟨0, 0, 0, 0⟩ := by
  decide +kernel

theorem cube_avg : groupAvg cubeGroup (fun g => (cubeTriplet g).trace) = 0 := by
  rw [show (fun g => (cubeTriplet g).trace) = fun g => colourChar cubeGroup g from rfl,
    groupAvg_cubeGroup]
  have e : ∑ k : Fin 24, colourChar cubeGroup (cubeElt k) =
      Exact.ZOP.toComplex (∑ k : Fin 24, Exact.M3Z.trace (cubeE k)) := by
    rw [toComplex_sum]
    exact Finset.sum_congr rfl fun k _ => char_cubeElt k
  rw [e, cube_sum]
  simp [Exact.ZOP.toComplex]

theorem a5_sum : zsum (fun n => trA5 n) 60 = ⟨0, 0, 0, 0⟩ := by
  decide +kernel

theorem a5_cube : zsum (fun n => trA5 n ^ 3) 60 = ⟨480, 0, 0, 0⟩ := by
  decide +kernel

theorem ico_avg : groupAvg icoGroup (fun g => (subTriplet icoGroup g).trace) = 0 := by
  rw [show (fun g => (subTriplet icoGroup g).trace) = fun g => colourChar icoGroup g from
    rfl, groupAvg_icoGroup]
  have e : ∑ n ∈ Finset.range 60, colourChar icoGroup (icoEltN n) =
      Exact.ZOP.toComplex (zsum (fun n => trA5 n) 60) / 2 := by
    rw [toComplex_zsum, Finset.sum_div]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_range] at hn
    rw [icoEltN_eq n hn, char_icoElt]
  rw [e, a5_sum]
  simp [Exact.ZOP.toComplex]

theorem ico_avg_cube : groupAvg icoGroup (fun g => colourChar icoGroup g ^ 3) = 1 := by
  rw [groupAvg_icoGroup]
  have e : ∑ n ∈ Finset.range 60, colourChar icoGroup (icoEltN n) ^ 3 =
      Exact.ZOP.toComplex (zsum (fun n => trA5 n ^ 3) 60) / 8 := by
    rw [toComplex_zsum, Finset.sum_div]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_range] at hn
    rw [icoEltN_eq n hn, char_icoElt, Exact.ZOP.toComplex_pow]
    ring
  rw [e, a5_cube]
  simp [Exact.ZOP.toComplex]
  norm_num

theorem sum_omega : ∑ j : Multiplicative (ZMod 3),
    Exact.omega ^ (Multiplicative.toAdd j).val = 0 := by
  rw [show (∑ j : Multiplicative (ZMod 3), Exact.omega ^ (Multiplicative.toAdd j).val) =
    ∑ a : Fin 3, Exact.omega ^ (a : ℕ) from rfl, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  linear_combination Exact.omega_sq_add

theorem c3a5_avg : groupAvg C3A5 (fun x => (c3a5Triplet x).trace) = 0 := by
  have hchar : ∀ x : C3A5, (c3a5Triplet x).trace =
      Exact.omega ^ (Multiplicative.toAdd x.1).val * colourChar icoGroup x.2 := by
    intro x
    rw [show (c3a5Triplet x).trace = C3A5.char x from rfl, char_C3A5]
  rw [groupAvg, finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
  simp only [hchar, ← Finset.mul_sum, ← Finset.sum_mul, sum_omega, zero_mul, mul_zero]

theorem c3a5_avg_normSq :
    groupAvg C3A5 (fun x => (c3a5Triplet x).trace * conj (c3a5Triplet x).trace) = 1 := by
  rw [show (fun x => (c3a5Triplet x).trace * conj (c3a5Triplet x).trace) =
    fun x : C3A5 => colourChar icoGroup x.2 ^ 2 from funext fun x => normSq_char_C3A5 x]
  exact (groupAvg_C3A5 (fun g => colourChar icoGroup g ^ 2)).trans ico_avg_sq

theorem c3a5_avg_cube : groupAvg C3A5 (fun x => (c3a5Triplet x).trace ^ 3) = 1 := by
  have hchar : ∀ x : C3A5, (c3a5Triplet x).trace ^ 3 = colourChar icoGroup x.2 ^ 3 := by
    intro x
    rw [show (c3a5Triplet x).trace = C3A5.char x from rfl, char_C3A5, mul_pow, ← pow_mul,
      mul_comm (Multiplicative.toAdd x.1).val 3, pow_mul, Exact.omega_pow_three, one_pow,
      one_mul]
  simp only [hchar]
  exact (groupAvg_C3A5 (fun g => colourChar icoGroup g ^ 3)).trans ico_avg_cube

theorem val_sum : classSum (fun t => t) = ⟨0, 0, 0, 0⟩ := by
  decide +kernel

theorem val_cube : classSum (fun t => t * t * t) = ⟨1080, 0, 0, 0⟩ := by
  decide +kernel

theorem val_avg : groupAvg valentiner (fun g => (subTriplet valentiner g).trace) = 0 := by
  rw [show (fun g => (subTriplet valentiner g).trace) =
    fun g => (fun z : ℂ => z) (colourChar valentiner g) from rfl,
    avg_exact (fun z => z) (fun t => t) (fun t => rfl) 0 val_sum]
  simp

theorem val_avg_cube :
    groupAvg valentiner (fun g => (subTriplet valentiner g).trace ^ 3) = 1 := by
  rw [show (fun g => (subTriplet valentiner g).trace ^ 3) =
    fun g => (fun z : ℂ => z ^ 3) (colourChar valentiner g) from rfl,
    avg_exact (fun z => z ^ 3) (fun t => t * t * t)
      (fun t => by rw [Exact.ZOP.toComplex_mul, Exact.ZOP.toComplex_mul]; ring) 1080 val_cube]
  norm_num

/-- The fixed vectors of `SU(3)` are fixed by `C₃ × A₅`, whose triplet factors through it. -/
theorem endFixed_su3_le (ord : LinearOrder (Edge.Mode (Fin 3) (Fin 2))) (k : ℕ) :
    endFixed su3Triplet ord k ≤ endFixed c3a5Triplet ord k := fun _ hv =>
  Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hv).1,
    fun h => (Submodule.mem_inf.mp hv).2 (C3A5.triplet h.1, C3A5.triplet h.2)⟩

end StringLine

open PathCanvas in
/-- **Proposition 13.1** (colourless states of a path). On a path whose matter sits at the two
ends, a colourless state depends on the links only through their product, the holonomy
`P = U_R ⋯ U_1`, and the colourless states of the path are the colourless states of one edge with
link `P`. With a quark source at `x₀`, an antiquark source at `x_R` and `d` slots at each end, their
number with `k` dynamical quarks is the coefficient of `z^k` in
`⟨χ(g) conj(χ(g)) det(1 + z g)^{2d}⟩_G`. -/
@[book "prop:ml-path"]
theorem mlPath : Statement.mlPath := by
  refine ⟨fun G _ N _ _ Γ R hR => ⟨fun ψ hψ U U' hUU' => ?_, edgeEquiv hR Γ,
    edgeEquiv_apply hR Γ⟩, fun G _ _ C S _ _ _ _ ρ ord R hR k => ?_⟩
  · rw [eq_std hR hψ U, eq_std hR hψ U', hUU']
  · have hsec : quarkSector R k = Submodule.pi Set.univ
        (fun _ : (Canvas.path R).skeleton.LinkTable G =>
          ({ carrier := {v | ∀ y, v y ≠ 0 → (fun y : (C × C) × Finset (Edge.Mode C S) =>
                y.2.card = k) y}
             add_mem' := fun {v w} hv hw n hn => by
               by_cases h : v n = 0
               · exact hw n (by simpa [h] using hn)
               · exact hv n h
             zero_mem' := fun n hn => absurd rfl hn
             smul_mem' := fun c v hv n hn => hv n (right_ne_zero_of_mul hn) } :
            Submodule ℂ ((C × C) × Finset (Edge.Mode C S) → ℂ))) := by
      ext ψ
      simp only [Submodule.mem_pi, Set.mem_univ, true_implies]
      rfl
    rw [hsec, finrank_colourless_sector hR _ (fun y => y.2.card = k)
      (fun h y y' hne => endMatter_respects ρ (Edge.conjTriplet ρ) ρ ord k h y y' hne)]
    simp only [sum_endMatter_diag, trace_conjTriplet]
    rw [Polynomial.coeff_smul, Polynomial.finsetSum_coeff, smul_eq_mul]
    simp only [Polynomial.coeff_C_mul]

open StringLine ColourGroups Classical in
/-- **Theorem 13.2** (the string). With a quark source at `x₀` and an antiquark source at `x_R`
and no dynamical quarks, each of the five colour groups has one colourless line, spanned by the
string `ψ_{cc'} = (U_1⁻¹ ⋯ U_R⁻¹)_{cc'}`; on every link its table lies in the conjugate triplet
block, so its electric energy is `κ E₃ R`. With two quark sources there is a colourless state
exactly when the triplet is real, `⟨χ²⟩ = 1`, and it is the same string. -/
@[book "thm:ml-string"]
theorem mlString : Statement.mlString := by
  unfold Statement.mlString
  intro real claims declared
  have hdecl : ∀ (G : Type) [Group G] [Fintype G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ),
      (∀ g, ρ g ∈ Matrix.unitaryGroup (Fin 3) ℂ) → HasKey ρ →
      groupAvg G (fun g => (ρ g).trace ^ 2) = (if real G ρ then 1 else 0) → declared G ρ := by
    intro G _ _ ρ hunit hk havg
    refine ⟨fun ι _ d σ hσ E E₃ hE R _ κ => ?_, havg⟩
    exact electric_string hunit (electricEnergy σ E) E₃
      (electricEnergy_conj (irreducible hk) hσ E E₃ hE) κ
  obtain ⟨xc, hxc⟩ := c3a5_omega
  obtain ⟨xv, hxv⟩ := val_omega
  obtain ⟨xs, hxs⟩ := su3_omega
  refine ⟨claims_of cubeTriplet_unitary cube_key (Or.inl cubeTriplet_real),
    claims_of (subTriplet_unit icoGroup) ico_key (Or.inl ico_real),
    claims_of c3a5_unit c3a5_key (Or.inr ⟨xc, hxc⟩),
    claims_of (subTriplet_unit valentiner) val_key (Or.inr ⟨xv, hxv⟩),
    claims_of su3_unit su3_key (Or.inr ⟨xs, hxs⟩),
    hdecl _ _ cubeTriplet_unitary cube_key ?_, hdecl _ _ (subTriplet_unit icoGroup) ico_key ?_,
    hdecl _ _ c3a5_unit c3a5_key ?_, hdecl _ _ (subTriplet_unit valentiner) val_key ?_⟩
  · rw [ite_eq_left cubeTriplet_real]
    exact cube_avg_sq
  · rw [ite_eq_left ico_real]
    exact ico_avg_sq
  · rw [ite_eq_right (not_real_of_omega hxc)]
    exact c3a5_avg_sq
  · rw [ite_eq_right (not_real_of_omega hxv)]
    exact val_avg_sq

open StringLine ColourGroups Classical in
/-- **Proposition 13.3** (the screening number). With a quark source at `x₀`, an antiquark source
at `x_R` and two slots at each end, the least number of dynamical quarks with which both sources
are colourless without flux is `2` for a real triplet and `3` for a complex one: four states with
one quark at each source, or six with the antisymmetric pair at the quark source in the slots
`s ≤ t` and one quark at the antiquark source. -/
@[book "prop:ml-screening"]
theorem mlScreening : Statement.mlScreening := by
  unfold Statement.mlScreening
  intro real claims
  obtain ⟨xc, hxc⟩ := c3a5_omega
  obtain ⟨xv, hxv⟩ := val_omega
  obtain ⟨xs, hxs⟩ := su3_omega
  have hc3 := complex_counts (ρ := c3a5Triplet) (fun x => (C3A5.triplet x).2) c3a5_avg
    c3a5_avg_normSq c3a5_avg_sq c3a5_avg_cube
  have hcube := screening_of (ρ := cubeTriplet) cubeTriplet_unitary
    (fun g => (Matrix.mem_specialUnitaryGroup_iff.mp (cubeTriplet_mem g)).2)
    (fun _ => real_counts cubeTriplet_mem cubeTriplet_real cube_avg cube_avg_sq)
    (fun h => absurd cubeTriplet_real h)
  have hico := screening_of (ρ := subTriplet icoGroup) (subTriplet_unit icoGroup)
    (fun g => (Matrix.mem_specialUnitaryGroup_iff.mp g.1.2).2)
    (fun _ => real_counts (ρ := subTriplet icoGroup) (fun g => g.1.2) ico_real ico_avg ico_avg_sq)
    (fun h => absurd ico_real h)
  have hc3a5 := screening_of (ρ := c3a5Triplet) c3a5_unit
    (fun x => (Matrix.mem_specialUnitaryGroup_iff.mp (C3A5.triplet x).2).2)
    (fun h => absurd h (not_real_of_omega hxc))
    (fun _ ord => ⟨(hc3 ord).1, (hc3 ord).2.1, (hc3 ord).2.2.1, (hc3 ord).2.2.2.le⟩)
  have hval := screening_of (ρ := subTriplet valentiner) (subTriplet_unit valentiner)
    (fun g => (Matrix.mem_specialUnitaryGroup_iff.mp g.1.2).2)
    (fun h => absurd h (not_real_of_omega hxv))
    (fun _ ord => by
      obtain ⟨a, b, c, d⟩ := complex_counts (ρ := subTriplet valentiner) (fun g => g.1.2) val_avg
        avg_normSq val_avg_sq val_avg_cube ord
      exact ⟨a, b, c, d.le⟩)
  have hsu3 := screening_of (ρ := su3Triplet) su3_unit
    (fun g => (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2)
    (fun h => absurd h (not_real_of_omega hxs))
    (fun _ ord => by
      obtain ⟨a, b, c, d⟩ := hc3 ord
      exact ⟨eq_bot_iff.mpr ((endFixed_su3_le ord 0).trans a.le),
        eq_bot_iff.mpr ((endFixed_su3_le ord 1).trans b.le),
        eq_bot_iff.mpr ((endFixed_su3_le ord 2).trans c.le),
        (Submodule.finrank_mono (endFixed_su3_le ord 3)).trans d.le⟩)
  exact ⟨hcube, hico, hc3a5, hval, hsu3⟩

open StringLine ColourGroups Classical in
/-- **Proposition 13.4** (where the string and screened levels cross). The string has the level
`κ E₃ R` and every minimal zero-flux screened state the level `k_min M`, `k_min = 2` for a real
triplet and `3` for a complex one, so the string is lower while `κ E₃ R < k_min M` and a screened
state beyond; with `E₃ = 4/3` they cross at `R = 3M/(2κ)` and `R = 9M/(4κ)`. The hop conserves
the quark number, and the two states lie in different sectors. -/
@[book "prop:ml-breaking"]
theorem mlBreaking : Statement.mlBreaking := by
  unfold Statement.mlBreaking
  intro real kmin claims declared
  have hdecl : ∀ (G : Type) [Group G] [Fintype G] (ρ : G →* Matrix (Fin 3) (Fin 3) ℂ),
      HasKey ρ → declared G ρ := fun G _ _ ρ hk ι _ d σ hσ E hE E₃ hE₃ =>
    ⟨electricEnergy_conj (irreducible hk) hσ E E₃ hE₃, electricEnergy_const hσ E hE⟩
  exact ⟨breaking_of cubeTriplet_unitary, breaking_of (subTriplet_unit icoGroup),
    breaking_of c3a5_unit, breaking_of (subTriplet_unit valentiner), breaking_of su3_unit,
    hdecl _ _ cube_key, hdecl _ _ ico_key, hdecl _ _ c3a5_key, hdecl _ _ val_key⟩


/-! ## Non-vacuity -/

section NonVacuity

open ColourGroups

/-- An order of the modes of one edge with two slots at each end. -/
@[instance_reducible]
noncomputable def twoSlotOrder : LinearOrder (Edge.Mode (Fin 3) (Fin 2)) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective

/-- Proposition 13.1 on the path of one edge with the matter of the string model, two slots at
each end, over the cube group: the hypotheses are met. -/
example :=
  mlPath.1 cubeGroup _ (PathCanvas.endMatter cubeTriplet (Edge.conjTriplet cubeTriplet)
    cubeTriplet twoSlotOrder) 1 one_pos

/-- The count of Proposition 13.1 on the path of one edge over the cube group with two slots at
each end, with no dynamical quark. -/
example :=
  mlPath.2 cubeGroup (Fin 3) (Fin 2) cubeTriplet twoSlotOrder 1 one_pos 0

/-- Theorem 13.2 on the path of one edge over the cube group: the string is not zero. -/
example : PathCanvas.string 1 cubeTriplet ≠ 0 :=
  (mlString.1 1 one_pos).2.1

/-- Proposition 13.3 on the path of one edge over the cube group, a real triplet: four zero-flux
states with two quarks. -/
example : Module.finrank ℂ ↥(PathCanvas.zeroFlux 1 (PathCanvas.endMatter cubeTriplet
    (Edge.conjTriplet cubeTriplet) cubeTriplet twoSlotOrder) ⊓ PathCanvas.quarkSector 1 2) = 4 :=
  ((mlScreening.1 twoSlotOrder 1 one_pos).1 cubeTriplet_real).2.2.2

/-- Proposition 13.3 on the path of one edge over `C₃ × A₅`, a complex triplet: six zero-flux
states with three quarks. -/
example : Module.finrank ℂ ↥(PathCanvas.zeroFlux 1 (PathCanvas.endMatter c3a5Triplet
    (Edge.conjTriplet c3a5Triplet) c3a5Triplet twoSlotOrder) ⊓ PathCanvas.quarkSector 1 3) = 6 :=
  ((mlScreening.2.2.1 twoSlotOrder 1 one_pos).2
    (StringLine.not_real_of_omega StringLine.c3a5_omega.choose_spec)).2.2.2.2

/-- Proposition 13.4 on the cube group: a complete family of irreducible representations exists,
and its declared electric energy with the level `4/3` on the nontrivial blocks and `0` on the
trivial one meets the hypotheses on `X` with `E₃ = 4/3`. -/
example : ∃ X : (cubeGroup → ℂ) → (cubeGroup → ℂ),
    (∀ f ∈ block (Edge.conjTripletRep cubeTriplet), X f = ((4 / 3 : ℚ) : ℂ) • f) ∧
      ∀ c : ℂ, X (fun _ => c) = 0 := by
  classical
  obtain ⟨n, d, σ, h1, h2, h3⟩ := (mtBlocks cubeGroup).1
  let E : Fin n → ℚ := fun i => if (σ i).IsTrivial then 0 else 4 / 3
  have hE : IsEnergyTable σ E := fun i =>
    ⟨fun h => by simp [E, h], fun h => by simp only [E, h, ite_false]; norm_num⟩
  have hE3 : ∀ i, Nonempty ((Edge.conjTripletRep cubeTriplet).Equiv (σ i)) → E i = 4 / 3 := by
    rintro i ⟨e⟩
    have : ¬ (σ i).IsTrivial := fun h =>
      ThereAndBack.not_isTrivial_tripletRep (ρ := Edge.conjTriplet cubeTriplet)
        (ThereAndBack.conjTripletRep_irreducible CubeGroup.isIrreducible_tripletRep)
        (ThereAndBack.isTrivial_of_equiv e h)
    simp [E, this]
  exact ⟨electricEnergy σ E, mlBreaking.2.2.2.2.2.1 (Fin n) d σ ⟨h1, h2, h3⟩ E hE (4 / 3) hE3⟩

end NonVacuity

end Artform
