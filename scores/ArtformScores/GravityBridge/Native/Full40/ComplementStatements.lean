import ArtformScores.GravityBridge.Native.Full40.ComplementDefs

/-! # Both diagonal transport paths in the native complement -/

namespace Artform.Scores.GravityBridge.Native.Full40.Statement

/-- **GAC2:native-five-summand-complement**
(both diagonal transport paths in the native complement). -/
@[ledger "GAC2:native-five-summand-complement"]
def complementLaw : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    (∀ (F0 Fk Fl Fkl Ak Al SkAl SlAk C : Frame K),
    fiveComplement F0 Fk Fl Fkl Fkl Ak Al SkAl SlAk C =
      cornerMean F0 Fk Fl Fkl - commutator (transportMean Ak Al SkAl SlAk) C) ∧
    (∀ (w0 wk wl wkl : Frame K),
    transportMean (wk - w0) (wl - w0) (wkl - wk) (wkl - wl) =
      cornerMean w0 wk wl wkl - w0) ∧
    (∀ (w0 wk wl wkl C : Frame K),
    fourCornerGauge w0 wk wl wkl C -
      commutator (transportMean (wk - w0) (wl - w0) (wkl - wk) (wkl - wl)) C =
        commutator w0 C) ∧
    (∀ (Ak : Frame K),
    transportMean Ak 0 0 0 = (3 / 8 : K) • Ak)

end Artform.Scores.GravityBridge.Native.Full40.Statement
