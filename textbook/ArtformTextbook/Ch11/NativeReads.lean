import ArtformTextbook.Ch11.CubeGroup
import ArtformTextbook.Ch11.Statements.Response

/-!
# Six native sign reads on the cube group (Proposition 11.8)

The kernel of a sign response on the cube group is `(1/24) N_D(c)` at a rotation of class `c`,
with the integer `N_D(c) = Σ_ρ r_D(ρ) d_ρ χ_ρ(c)` read off the character table (`numZ`). It lies
in `R₈` exactly when `3` divides `N_D(c)` (`Exact.intCast_div_24_mem_R8C_iff`), and every class
contains a rotation, so whether a sign response is native is decided on the five classes and the
thirty-two sets `D` by the kernel. The counts of rotations come from the enumeration of the cube
group by pairs `(σ, s)` (`Ch11/CubeGroup.lean`).
-/

namespace Artform

/-- The five classes of the cube group form a finite type. -/
instance CubeClass.fintype : Fintype CubeClass where
  elems := {.identity, .edgeHalfTurn, .faceHalfTurn, .vertexThirdTurn, .faceQuarterTurn}
  complete x := by cases x <;> simp

namespace NativeReads

/-- The character table of the cube group with integer entries. -/
def tabZ : CubeBlock → CubeClass → ℤ
  | .one, _ => 1
  | .sign, .identity => 1
  | .sign, .edgeHalfTurn => -1
  | .sign, .faceHalfTurn => 1
  | .sign, .vertexThirdTurn => 1
  | .sign, .faceQuarterTurn => -1
  | .two, .identity => 2
  | .two, .edgeHalfTurn => 0
  | .two, .faceHalfTurn => 2
  | .two, .vertexThirdTurn => -1
  | .two, .faceQuarterTurn => 0
  | .threeS, .identity => 3
  | .threeS, .edgeHalfTurn => 1
  | .threeS, .faceHalfTurn => -1
  | .threeS, .vertexThirdTurn => 0
  | .threeS, .faceQuarterTurn => -1
  | .threeR, .identity => 3
  | .threeR, .edgeHalfTurn => -1
  | .threeR, .faceHalfTurn => -1
  | .threeR, .vertexThirdTurn => 0
  | .threeR, .faceQuarterTurn => 1

theorem cubeCharTable_eq (ρ : CubeBlock) (c : CubeClass) : cubeCharTable ρ c = (tabZ ρ c : ℂ) := by
  cases ρ <;> cases c <;> simp [cubeCharTable, tabZ]

/-- The integer `N_D(c) = Σ_ρ r_D(ρ) d_ρ χ_ρ(c)`. -/
def numZ (D : Finset CubeBlock) (c : CubeClass) : ℤ :=
  ∑ ρ, (if ρ ∈ D then -1 else 1) * tabZ ρ .identity * tabZ ρ c

/-- The kernel of a sign response at a rotation is `N_D(c)/24`. -/
theorem kernel_eq (D : Finset CubeBlock) (g : cubeGroup) :
    responseKernel cubeChar (fun ρ => cubeCharTable ρ .identity) (signResponse D) g =
      (numZ D (cubeClassOf g) : ℂ) / 24 := by
  rw [responseKernel, CubeGroup.card, numZ]
  simp only [cubeChar, cubeCharTable_eq, signResponse]
  push_cast
  rw [div_eq_inv_mul]

/-- Every class contains a rotation. -/
theorem exists_of_class (c : CubeClass) : ∃ g : cubeGroup, cubeClassOf g = c := by
  have h : ∀ c : CubeClass, ∃ p : CubeGroup.Pair, CubeGroup.classOf p = c := by decide +kernel
  obtain ⟨p, hp⟩ := h c
  exact ⟨CubeGroup.toGroup p, by rw [CubeGroup.cubeClassOf_toGroup, hp]⟩

/-- A sign response is native exactly when `3` divides `N_D(c)` on every class. -/
theorem native_iff (D : Finset CubeBlock) :
    (∀ g, responseKernel cubeChar (fun ρ => cubeCharTable ρ .identity) (signResponse D) g ∈
      Exact.R8C) ↔ ∀ c, (3 : ℤ) ∣ numZ D c := by
  simp only [kernel_eq, Exact.intCast_div_24_mem_R8C_iff]
  constructor
  · intro h c
    obtain ⟨g, rfl⟩ := exists_of_class c
    exact h g
  · intro h g
    exact h _

theorem one_eq_of_class (g : cubeGroup) (hg : cubeClassOf g = .identity) : g = 1 := by
  obtain ⟨p, rfl⟩ := CubeGroup.exists_toGroup g
  rw [CubeGroup.cubeClassOf_toGroup] at hg
  have h : ∀ p : CubeGroup.Pair, CubeGroup.classOf p = .identity → p = ⟨(1, fun _ => 1),
      by decide⟩ := by decide +kernel
  rw [h p hg]
  apply Subtype.ext
  apply Subtype.ext
  exact signedPermMatrix_one

theorem class_one : cubeClassOf (1 : cubeGroup) = .identity := by
  have h : (1 : cubeGroup) = CubeGroup.toGroup ⟨(1, fun _ => 1), by decide⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    exact signedPermMatrix_one.symm
  rw [h, CubeGroup.cubeClassOf_toGroup]
  decide +kernel

end NativeReads

open NativeReads in
/-- **Proposition 11.8** (six native sign reads on the cube group). Allowing either sign on the
trivial block, of the thirty nonconstant sign assignments on `S₄`, exactly six have kernels in
`R₈`: `D = {3_r}`, `{3_s}`, `{3_r, 3_s}` and their complements. Complementing `D` negates the whole
kernel. Thus exactly three nonidentity responses obey the normalization `r(1) = 1` of
Definition 11.7: the three displayed sets. For `D = {3_r, 3_s}` the kernel is `-1/2` at the
identity, `+1/2` at each of the three half-turns about face axes, and zero elsewhere. For a single
triplet it is `±1/4` on the sixteen elements that are not third-turns. -/
@[book "prop:mt-native-reads"]
theorem mtNativeReads : Statement.mtNativeReads := by
  delta Statement.mtNativeReads
  intro k native six
  have hk : ∀ D g, k D g = (numZ D (cubeClassOf g) : ℂ) / 24 := kernel_eq
  have hnat : ∀ D, native D ↔ ∀ c, (3 : ℤ) ∣ numZ D c := native_iff
  refine ⟨by decide +kernel, fun D hD1 hD2 => ?_, by decide +kernel, fun D g => ?_, fun D => ?_,
    fun g => ?_, ?_, fun D hD g => ?_, ?_⟩
  · rw [hnat]
    revert D
    decide +kernel
  · have h : ∀ (D : Finset CubeBlock) c, numZ Dᶜ c = -numZ D c := by decide +kernel
    rw [hk, hk, h]
    push_cast
    ring
  · rw [hnat]
    revert D
    decide +kernel
  · rw [hk]
    by_cases h1 : g = 1
    · subst h1
      rw [class_one, ite_eq_left rfl]
      have : numZ {.threeR, .threeS} .identity = -12 := by decide +kernel
      rw [this]
      norm_num
    · rw [ite_eq_right h1]
      have hc : cubeClassOf g ≠ .identity := fun h => h1 (one_eq_of_class g h)
      have h : ∀ c : CubeClass, c ≠ .identity →
          numZ {.threeR, .threeS} c = if c = .faceHalfTurn then 12 else 0 := by decide +kernel
      rw [h _ hc]
      split_ifs <;> norm_num
  · rw [CubeGroup.card_subtype_eq _ (fun p => CubeGroup.classOf p = .faceHalfTurn)
      (fun p => by rw [CubeGroup.cubeClassOf_toGroup])]
    decide +kernel
  · rw [hk]
    have h : ∀ D ∈ ({{.threeR}, {.threeS}} : Finset (Finset CubeBlock)), ∀ c,
        (c ≠ .vertexThirdTurn → numZ D c = 6 ∨ numZ D c = -6) ∧
        (c = .vertexThirdTurn → numZ D c = 0) := by decide +kernel
    obtain ⟨h1, h2⟩ := h D hD (cubeClassOf g)
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rcases h1 hc with h | h
      · left
        rw [h]
        norm_num
      · right
        rw [h]
        norm_num
    · rw [h2 hc]
      norm_num
  · rw [CubeGroup.card_subtype_eq _ (fun p => CubeGroup.classOf p ≠ .vertexThirdTurn)
      (fun p => by rw [CubeGroup.cubeClassOf_toGroup])]
    decide +kernel

/-! ## Non-vacuity -/

/-- Proposition 11.8 on the book's running example, the cube group: its kernels are defined for
every set `D` of blocks, and the read with `D = {3_r, 3_s}`, the one the native tick uses, is the
`-1/2` at the identity rotation. -/
example : responseKernel cubeChar (fun ρ => cubeCharTable ρ .identity)
    (signResponse {.threeR, .threeS}) 1 = -1 / 2 := by
  have h := mtNativeReads.2.2.2.2.2.1 1
  rw [ite_eq_left rfl] at h
  exact h

end Artform
