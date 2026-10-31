import ArtformScores.GravityBridge.Defs

/-! # Original forty coordinates Gram and Hodge data -/

namespace Artform.Scores.GravityBridge.Native.Full40

variable {K : Type*} [Field K] [CharZero K]

abbrev Vec (K : Type*) := Fin 4 → K

abbrev Frame (K : Type*) := Matrix (Fin 4) (Fin 4) K

abbrev Biv (K : Type*) := Fin 6 → K

abbrev Connection (K : Type*) := Fin 4 → Biv K

abbrev Coordinate := (Fin 4 × Fin 4) ⊕ (Fin 4 × Fin 6)

abbrev Full (K : Type*) := Frame K × Connection K

variable {K : Type*} [Field K] [CharZero K]

def pack (x : Full K) : Coordinate → K :=
  Sum.elim (fun ij => x.1 ij.1 ij.2) (fun ia => x.2 ia.1 ia.2)

def unpack (x : Coordinate → K) : Full K :=
  (fun i j => x (Sum.inl (i, j)), fun i a => x (Sum.inr (i, a)))

def eta (i : Fin 4) : K := if i = 0 then -1 else 1
/-- Original ordered bivectors(01,02,03,23,31,12), as Lorentz matrices. -/
def lie (a : Biv K) : Frame K :=
  !![0, a 0, a 1, a 2; a 0, 0, a 5, -a 4;
     a 1, -a 5, 0, a 3; a 2, a 4, -a 3, 0]

def lieCoordinates (F : Frame K) : Biv K := ![F 0 1, F 0 2, F 0 3, F 2 3, F 3 1, F 1 2]

def metricVariation (F : Frame K) (i j : Fin 4) : K := eta i * F i j + eta j * F j i

def bivSign (a : Fin 6) : K := if a.val < 3 then -1 else 1

def bivPair (a b : Biv K) : K := ∑ i, bivSign i * a i * b i

def gramConvert (a : Biv K) : Biv K := fun i => bivSign i * a i

def internalStar (a : Biv K) : Biv K := ![-a 3, -a 4, -a 5, a 0, a 1, a 2]

def etaPair (u v : Vec K) : K := ∑ i, eta i * u i * v i

def frameGram (f : Frame K) : Frame K := fun i j => eta i * f i j

end Artform.Scores.GravityBridge.Native.Full40
