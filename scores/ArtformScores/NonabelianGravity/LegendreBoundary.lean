import ArtformScores.NonabelianGravity.LegendreBinding
import ArtformScores.NonabelianGravity.LegendreMatrix

/-! # Actual native endpoint covectors and a constrained relation-valued score -/
set_option autoImplicit false
namespace Artform.Scores.NonabelianGravity.Legendre
variable {K : Type*} [Field K] [CharZero K]

def background (i : Fin 40) : ℚ := if i = 22 ∨ i = 29 ∨ i = 36 then 1 else 0

noncomputable def pre (u v : Point K) : Point K :=
  -(fun i => (background i : K)) - (castMatrix oldH).mulVec u - (castMatrix mixed).mulVec v

noncomputable def post (u v : Point K) : Point K :=
  -(fun i => (background i : K)) + (castMatrix mixed).transpose.mulVec u +
    (castMatrix newH).mulVec v

abbrev Phase (K : Type*) := Point K × Point K

noncomputable def NativeRelation (a b : Phase K) : Prop :=
  a.2 = pre a.1 b.1 ∧ b.2 = post a.1 b.1

noncomputable def incomingKick (a : Phase K) : Phase K :=
  (a.1, a.2 + (fun i => (background i : K)) + (castMatrix oldH).mulVec a.1)

noncomputable def outgoingKick (a : Phase K) : Phase K :=
  (a.1, a.2 - (fun i => (background i : K)) + (castMatrix newH).mulVec a.1)

noncomputable def centralRelation (a b : Phase K) : Prop :=
  a.2 = -(castMatrix mixed).mulVec b.1 ∧ b.2 = (castMatrix mixed).transpose.mulVec a.1

noncomputable def ScoreRelation (a b : Phase K) : Prop :=
  ∃ c, centralRelation (incomingKick a) c ∧ outgoingKick c = b

omit [CharZero K] in
lemma relation_factorization (a b : Phase K) : NativeRelation a b ↔ ScoreRelation a b := by
  constructor
  · rintro ⟨hp, hq⟩
    refine ⟨(b.1, (castMatrix mixed).transpose.mulVec a.1), ⟨?_, rfl⟩, ?_⟩
    · dsimp [incomingKick]
      rw [hp]
      unfold pre
      abel
    · apply Prod.ext
      · rfl
      · dsimp [outgoingKick]
        rw [hq]
        unfold post
        abel
  · rintro ⟨c, ⟨hp, hq⟩, h⟩
    have hc := congrArg Prod.fst h
    change c.1 = b.1 at hc
    have hb : c.2 - (fun i => (background i : K)) +
        (castMatrix newH).mulVec c.1 = b.2 := congrArg Prod.snd h
    constructor
    · dsimp [incomingKick] at hp
      rw [hc] at hp
      unfold pre
      linear_combination hp
    · dsimp only [incomingKick] at hq
      rw [← hb, hq, hc]
      unfold post
      abel

end Artform.Scores.NonabelianGravity.Legendre
