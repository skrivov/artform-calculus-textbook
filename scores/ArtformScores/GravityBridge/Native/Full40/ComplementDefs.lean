import ArtformScores.GravityBridge.Native.Full40.Coordinates
import ArtformScores.GravityBridge.Native.Full40.Plaquette

/-! # Both diagonal transport paths in the native complement -/

namespace Artform.Scores.GravityBridge.Native.Full40

variable {K : Type*} [Field K] [CharZero K]

def cornerMean (F0 Fk Fl Fkl : Frame K) : Frame K := (1 / 4 : K) • (F0 + Fk + Fl + Fkl)

def transportMean (Ak Al SkAl SlAk : Frame K) : Frame K :=
  (1 / 8 : K) • ((3 : K) • Ak + SlAk + (3 : K) • Al + SkAl)

def fiveComplement (F0 Fk Fl Fkl Flk Ak Al SkAl SlAk C : Frame K) : Frame K :=
  (1 / 4 : K) • F0 + (1 / 4 : K) • (Fk - commutator Ak C) +
    (1 / 4 : K) • (Fl - commutator Al C) +
    (1 / 8 : K) • (Fkl - commutator (Ak + SkAl) C) +
    (1 / 8 : K) • (Flk - commutator (Al + SlAk) C)

def fourCornerGauge (w0 wk wl wkl C : Frame K) : Frame K :=
  cornerMean (commutator w0 C) (commutator wk C) (commutator wl C) (commutator wkl C)

end Artform.Scores.GravityBridge.Native.Full40
