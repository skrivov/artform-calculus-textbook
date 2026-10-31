import ArtformScores.Nonabelian.Descent

/-! # Integer stage certificates for both six-phase comparisons -/
set_option autoImplicit false
namespace Artform.Scores.Nonabelian
def freeStage : Fin 7 → Fin 11 → ℤ := ![
  ![0,1,0,0,0,0,0,0,0,0,0],
  ![0,1,0,0,0,0,0,0,0,0,0],
  ![0,-2,0,0,1,1,0,0,1,0,0],
  ![-6,0,-6,3,0,0,3,3,0,3,3],
  ![-6,0,-6,3,0,0,3,3,0,3,3],
  ![27,0,27,0,0,0,0,0,0,0,0],
  ![0,81,0,0,0,0,0,0,0,0,0]]
def stageDivisor : Fin 7 → ℚ := ![1,1,3,9,9,27,81]
def checkedStage (active : Bool) (k : Fin 7) : Fin 11 → ℚ :=
  fun i => ((if active then stage k i else freeStage k i) : ℚ)/stageDivisor k
def certificateGate (active : Bool) : Fin 6 → Gate :=
  ![.curvature active,.electric false,.electric true,
    .curvature active,.electric false,.electric true]
def sourceVector : Fin 11 → ℚ := Pi.single 1 1
lemma checked_source (active : Bool) : checkedStage active 0=sourceVector := by
  cases active <;> decide +kernel
lemma checked_transition (active : Bool) (k : Fin 6) :
    (orbitMatrix (certificateGate active k)).mulVec (checkedStage active k.castSucc)=
      checkedStage active k.succ := by
  cases active <;> fin_cases k <;> decide +kernel
lemma checked_free : checkedStage false 6=sourceVector := by decide +kernel
lemma two_tick_orbit (active : Bool) :
    (compileOrbit (tickWord active++tickWord active)).mulVec sourceVector=
      checkedStage active 6 := by
  simp only [tickWord,List.cons_append,List.nil_append,compileOrbit,Matrix.one_mul,
    ← Matrix.mulVec_mulVec]
  have h0 : (orbitMatrix (.curvature active)).mulVec (checkedStage active 0)=
      checkedStage active 1 := checked_transition active 0
  have h1 : (orbitMatrix (.electric false)).mulVec (checkedStage active 1)=
      checkedStage active 2 := checked_transition active 1
  have h2 : (orbitMatrix (.electric true)).mulVec (checkedStage active 2)=
      checkedStage active 3 := checked_transition active 2
  have h3 : (orbitMatrix (.curvature active)).mulVec (checkedStage active 3)=
      checkedStage active 4 := checked_transition active 3
  have h4 : (orbitMatrix (.electric false)).mulVec (checkedStage active 4)=
      checkedStage active 5 := checked_transition active 4
  have h5 : (orbitMatrix (.electric true)).mulVec (checkedStage active 5)=
      checkedStage active 6 := checked_transition active 5
  rw [← checked_source active,h0,h1,h2,h3,h4,h5]
end Artform.Scores.Nonabelian
