import ArtformScores.GravityBridge.Native.Full40.Split
/-! # The original metric Cauchy organization and exact inverses -/
namespace Artform.Scores.GravityBridge.Native.MetricCut
open Matrix
variable {K : Type*} [Field K] [CharZero K]
abbrev SVec (K : Type*) := Fin 3 → K
abbrev SMat (K : Type*) := Matrix (Fin 3) (Fin 3) K
def dot3 (u v : SVec K) : K := ∑ i, u i * v i
def rho2 (k : SVec K) : K := dot3 k k
def outer3 (u v : SVec K) : SMat K := fun i j => u i * v j
def projector3 (k : SVec K) : SMat K := 1 - (rho2 k)⁻¹ • outer3 k k
def spatialGradient (j : K) (k u : SVec K) : SMat K :=
  j • (outer3 k u + outer3 u k)
def spatialCompose (j : K) (k : SVec K) (q : SMat K) (sigma : K) (u : SVec K) : SMat K :=
  q + sigma • projector3 k + spatialGradient j k u
def coulomb3 (j : K) (k : SVec K) (m : SMat K) : SVec K :=
  (j * rho2 k)⁻¹ • (m *ᵥ k - (dot3 k (m *ᵥ k) / (2 * rho2 k)) • k)
def scalar3 (k : SVec K) (m : SMat K) : K :=
  (trace m - dot3 k (m *ᵥ k) / rho2 k) / 2
def tt3 (j : K) (k : SVec K) (m : SMat K) : SMat K :=
  m - scalar3 k m • projector3 k - spatialGradient j k (coulomb3 j k m)
@[ext]
structure CauchyData (K : Type*) where
  spatial : SMat K
  spatialVelocity : SMat K
  shift : SVec K
  lapse : K
  shiftVelocity : SVec K
  lapseVelocity : K
  deriving DecidableEq
@[ext]
structure Organized (K : Type*) where
  tt : SMat K
  ttVelocity : SMat K
  u : SVec K
  velocity : SVec K
  temporalCoordinate : K
  lapse : K
  shiftVelocity : SVec K
  lapseVelocity : K
  hamiltonian : K
  momentum : SVec K
  deriving DecidableEq
def momentum3 (j : K) (k : SVec K) (m : SMat K) (shift : SVec K) : SVec K :=
  (2 : K)⁻¹ • (rho2 k • shift - dot3 k shift • k +
    j • (m *ᵥ k - trace m • k))
def organize (j : K) (k : SVec K) (x : CauchyData K) : Organized K where
  tt := tt3 j k x.spatial
  ttVelocity := tt3 j k x.spatialVelocity
  u := coulomb3 j k x.spatial
  velocity := coulomb3 j k x.spatialVelocity
  temporalCoordinate := (dot3 k x.shift - dot3 k (coulomb3 j k x.spatialVelocity)) /
    (j * rho2 k)
  lapse := x.lapse
  shiftVelocity := x.shiftVelocity
  lapseVelocity := x.lapseVelocity
  hamiltonian := rho2 k * scalar3 k x.spatial
  momentum := momentum3 j k x.spatialVelocity x.shift
def reconstruct (j : K) (k : SVec K) (z : Organized K) : CauchyData K where
  spatial := spatialCompose j k z.tt (z.hamiltonian / rho2 k) z.u
  spatialVelocity := spatialCompose j k z.ttVelocity
    (j * dot3 k z.momentum / rho2 k) z.velocity
  shift := (2 / rho2 k) •
    (z.momentum - (dot3 k z.momentum / rho2 k) • k) +
    z.velocity + (j * z.temporalCoordinate) • k
  lapse := z.lapse
  shiftVelocity := z.shiftVelocity
  lapseVelocity := z.lapseVelocity
def fixedN4Target (j : K) (k : SVec K) (q p : SMat K) (v4 : K) (X4 : SVec K) :
    CauchyData K where
  spatial := q + (4 * v4) • (1 : SMat K)
  spatialVelocity := (2 : K) • p + (2 : K) • spatialGradient j k X4
  shift := 0
  lapse := 0
  shiftVelocity := (-2 * j * v4) • k
  lapseVelocity := 0
def symmetricCauchy (x : CauchyData K) : Prop :=
  (∀ i l, x.spatial i l = x.spatial l i) ∧
    (∀ i l, x.spatialVelocity i l = x.spatialVelocity l i)
def symmetricOrganized (z : Organized K) : Prop :=
  (∀ i l, z.tt i l = z.tt l i) ∧
    (∀ i l, z.ttVelocity i l = z.ttVelocity l i)
end Artform.Scores.GravityBridge.Native.MetricCut
