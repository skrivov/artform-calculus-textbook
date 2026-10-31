import ArtformScores.GravityBridge.Native.Full40.ComplementStatements

/-! # Both diagonal transport paths in the native complement -/

namespace Artform.Scores.GravityBridge.Native.Full40

variable {K : Type*} [Field K] [CharZero K]

lemma five_summand_complement (F0 Fk Fl Fkl Ak Al SkAl SlAk C : Frame K) :
    fiveComplement F0 Fk Fl Fkl Fkl Ak Al SkAl SlAk C =
      cornerMean F0 Fk Fl Fkl - commutator (transportMean Ak Al SkAl SlAk) C := by
  ext i j
  simp [fiveComplement, cornerMean, commutator, transportMean,
    Matrix.mul_apply, Fin.sum_univ_succ]
  ring
lemma transport_gauge_mean (w0 wk wl wkl : Frame K) :
    transportMean (wk - w0) (wl - w0) (wkl - wk) (wkl - wl) =
      cornerMean w0 wk wl wkl - w0 := by
  ext i j
  simp [transportMean, cornerMean]
  ring
lemma mixed_complement_gauge (w0 wk wl wkl C : Frame K) :
    fourCornerGauge w0 wk wl wkl C -
      commutator (transportMean (wk - w0) (wl - w0) (wkl - wk) (wkl - wl)) C =
        commutator w0 C := by
  rw [transport_gauge_mean]
  ext i j
  simp [fourCornerGauge, cornerMean, commutator, Matrix.mul_apply, Fin.sum_univ_succ]
  ring
lemma diagonal_paths_matter (Ak : Frame K) :
    transportMean Ak 0 0 0 = (3 / 8 : K) • Ak := by
  ext i j
  simp [transportMean]
  ring

/-- **GAC2:native-five-summand-complement**
(both diagonal transport paths in the native complement). -/
@[ledger "GAC2:native-five-summand-complement"]
theorem complementLaw : Statement.complementLaw := by
  intro K _ _
  exact ⟨five_summand_complement,
    transport_gauge_mean,
    mixed_complement_gauge,
    diagonal_paths_matter⟩

/-! ## Non-vacuity -/
example : transportMean (lie ![1, 0, 0, 0, 0, 0]) 0 0 0 0 1 = (3 / 8 : ℚ) := by
  norm_num [transportMean, lie]

end Artform.Scores.GravityBridge.Native.Full40
