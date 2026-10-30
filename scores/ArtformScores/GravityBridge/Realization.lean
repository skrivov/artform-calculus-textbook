import ArtformScores.GravityBridge.Statements

/-! # Exact realization and the limits of visible readings -/

namespace Artform.Scores.GravityBridge

theorem invariant_iff_intertwines {Y H : Type*} (r : Realization Y H) (T : H → H) :
    r.Invariant T ↔ r.Intertwines T := by
  constructor
  · intro h y
    obtain ⟨z, hz⟩ := h y
    change T (r.embed y) = r.embed (r.read (T (r.embed y)))
    rw [← hz, r.recover z]
  · intro h y
    exact ⟨r.visible T y, (h y).symm⟩

theorem realization_iterate {Y H : Type*} (r : Realization Y H) (T : H → H)
    (h : r.Intertwines T) (n : ℕ) (y : Y) :
    T^[n] (r.embed y) = r.embed ((r.visible T)^[n] y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, h]

/-- **GAC:realization** (invariance and all-time realization). -/
@[ledger "GAC:realization"]
theorem invariantRealization : Statement.invariantRealization := by
  intro Y H r T
  refine ⟨invariant_iff_intertwines r T, ?_⟩
  intro h n y
  have hi := realization_iterate r T h n y
  exact ⟨hi, by rw [hi, r.recover]⟩

/-! ## Non-vacuity -/

/-- A visible variable with one retained auxiliary variable. -/
def scalarEmbedding : Realization ℚ (ℚ × ℚ) :=
  ⟨fun y => (y, 0), Prod.fst, fun _ => rfl⟩

/-- An honest autonomous restriction. -/
example : scalarEmbedding.Invariant (fun x => (x.1 + 1, 2 * x.2)) := by
  intro y
  exact ⟨y + 1, by simp [scalarEmbedding]⟩

/-- Equal visible readings at every time do not imply invariance. The unobserved
coordinate grows while the visible coordinate stays fixed. -/
example :
    (∀ (n : ℕ) (y : ℚ),
      scalarEmbedding.read ((fun x : ℚ × ℚ => (x.1, x.2 + 1))^[n]
        (scalarEmbedding.embed y)) =
        (scalarEmbedding.visible (fun x => (x.1, x.2 + 1)))^[n] y) ∧
    ¬ scalarEmbedding.Invariant (fun x => (x.1, x.2 + 1)) := by
  constructor
  · intro n y
    have hread : ∀ x : ℚ × ℚ,
        ((fun x : ℚ × ℚ => (x.1, x.2 + 1))^[n] x).1 = x.1 := by
      intro x
      induction n generalizing x with
      | zero => rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply]
        exact ih _
    change ((fun x : ℚ × ℚ => (x.1, x.2 + 1))^[n] (y, 0)).1 =
      (id : ℚ → ℚ)^[n] y
    simpa using hread (y, 0)
  · intro h
    obtain ⟨y, hy⟩ := h 0
    have hsecond := congrArg Prod.snd hy
    norm_num [scalarEmbedding] at hsecond

end Artform.Scores.GravityBridge
