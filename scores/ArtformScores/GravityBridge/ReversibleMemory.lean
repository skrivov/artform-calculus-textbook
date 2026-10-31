import ArtformScores.GravityBridge.ReversibleMemoryStatements
import ArtformScores.GravityBridge.Realization
import ArtformScores.GravityBridge.Memory

/-! # Reversible preparation, reset and finite information cost -/

namespace Artform.Scores.GravityBridge

lemma reversible_visible_injective {Y H : Type*} (r : Realization Y H) (T : H ≃ H)
    (h : r.Invariant T) : Function.Injective (r.visible T) := by
  intro x y hxy
  apply r.recover.injective
  apply T.injective
  have hi := (invariant_iff_intertwines r T).mp h
  exact (hi x).trans ((congrArg r.embed hxy).trans (hi y).symm)

lemma inverse_image_iff_surjective {Y H : Type*} (r : Realization Y H) (T : H ≃ H)
    (h : r.Invariant T) : r.Invariant T.symm ↔ Function.Surjective (r.visible T) := by
  have hi := (invariant_iff_intertwines r T).mp h
  constructor
  · intro hinv y
    obtain ⟨z, hz⟩ := hinv y
    refine ⟨z, ?_⟩
    have htz : T (r.embed z) = r.embed y := by rw [hz]; simp
    change r.read (T (r.embed z)) = y
    rw [htz, r.recover]
  · intro hs y
    obtain ⟨z, hz⟩ := hs y
    refine ⟨z, ?_⟩
    apply T.injective
    rw [hi z, hz]
    simp

lemma finite_visible_bijective {Y H : Type*} [Finite Y] (r : Realization Y H)
    (T : H ≃ H) (h : r.Invariant T) : Function.Bijective (r.visible T) := by
  have hi := reversible_visible_injective r T h
  exact ⟨hi, Finite.surjective_of_injective hi⟩

lemma fiber_memory_injective {X W M : Type*} (O : X → W) (m : X → M)
    (h : Function.Injective (fun x => (O x, m x))) (w : W) :
    Function.Injective (fun x : {x // O x = w} => m x.val) := by
  intro x y hm
  apply Subtype.ext
  apply h
  exact Prod.ext (x.property.trans y.property.symm) hm

lemma finite_fiber_memory_bound {X W M : Type*} [Finite M] (O : X → W) (m : X → M)
    (h : Function.Injective (fun x => (O x, m x))) (w : W) :
    Nat.card {x // O x = w} ≤ Nat.card M := by
  exact Nat.card_le_card_of_injective _ (fiber_memory_injective O m h w)

lemma reset_injective_iff {Y Z : Type*} [Nonempty Y] (z0 : Z) :
    Function.Injective (fun p : Y × Z => (p.1, z0)) ↔ Subsingleton Z := by
  constructor
  · intro h
    obtain ⟨y⟩ := ‹Nonempty Y›
    refine ⟨fun a b => ?_⟩
    have hab : (y, a) = (y, b) := h rfl
    exact congrArg Prod.snd hab
  · intro h a b hab
    have hf := congrArg (Prod.fst : Y × Z → Y) hab
    change a.1 = b.1 at hf
    exact Prod.ext hf (h.elim a.2 b.2)

/-- **GAC:reversible-memory** (invariant visible reversibility and retained information). -/
@[ledger "GAC:reversible-memory"]
theorem reversibleMemory : Statement.reversibleMemory := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Y H r T h
    exact ⟨reversible_visible_injective r T h, inverse_image_iff_surjective r T h⟩
  · intro Y H _ r T h
    exact finite_visible_bijective r T h
  · intro X W M _ O m h w
    exact ⟨fiber_memory_injective O m h w, finite_fiber_memory_bound O m h w⟩
  · intro Y Z _ z0
    exact reset_injective_iff z0

/-! ## Non-vacuity -/

def shiftInteger : ℤ ≃ ℤ where
  toFun z := z + 1
  invFun z := z - 1
  left_inv z := by dsimp; omega
  right_inv z := by dsimp; omega

def nonnegativeImage : Realization ℕ ℤ :=
  ⟨Int.ofNat, Int.toNat, by intro n; simp⟩

example : nonnegativeImage.Invariant shiftInteger := by
  intro n
  exact ⟨n + 1, by simp [nonnegativeImage, shiftInteger]⟩

example : ¬ Function.Surjective (nonnegativeImage.visible shiftInteger) := by
  intro h
  obtain ⟨n, hn⟩ := h 0
  simp [Realization.visible, nonnegativeImage, shiftInteger] at hn

example : ∀ x : ZMod 7,
    Matrix.mulVec (realize (whitehead (1 : (ZMod 7)ˣ)) : Matrix (Fin 2) (Fin 2) (ZMod 7))
      ![x, 0] = ![0, -x] := by
  intro x
  rw [whitehead_mat]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

example {M : Type*} [Finite M] (m : ZMod 7 → M)
    (h : Function.Injective (fun x : ZMod 7 => ((0 : ZMod 7), m x))) :
    7 ≤ Nat.card M := by
  have hi : Function.Injective m := by
    intro a b hab
    exact h (Prod.ext rfl hab)
  simpa using Nat.card_le_card_of_injective m hi

example : Function.Injective (fun x : ZMod 7 => ((0 : ZMod 7), -x)) := by
  intro a b h
  exact neg_injective (congrArg Prod.snd h)


def quarterEquiv7 : (ZMod 7 × ZMod 7) ≃ (ZMod 7 × ZMod 7) where
  toFun p := (p.2, -p.1)
  invFun p := (-p.2, p.1)
  left_inv p := by simp
  right_inv p := by simp

example : Function.Bijective
    ((⟨id, id, fun _ => rfl⟩ : Realization (ZMod 7 × ZMod 7) (ZMod 7 × ZMod 7)).visible
      quarterEquiv7) := by
  apply finite_visible_bijective
  intro y
  exact ⟨quarterEquiv7 y, rfl⟩

end Artform.Scores.GravityBridge
