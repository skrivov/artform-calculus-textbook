import ArtformScores.Gauge.Laurent
import ArtformScores.Gauge.Process
import ArtformScores.Gauge.Macro
import ArtformScores.Gauge.Spatial
import ArtformScores.Gauge.Coherent
import ArtformScores.Meta.Ledger

/-! # Gauge score applications: literal ledger claims -/
set_option autoImplicit false
namespace Artform.Scores.Gauge.Statement
open Artform Finset LaurentPolynomial Polynomial

/-- **GSC:canonical-filter** (reversal, fixed stencils and Weyl separation). -/
@[ledger "GSC:canonical-filter"]
def canonicalFilter : Prop :=
  (∀ (R : Type) [CommRing R] (P : Matrix (Fin 2) (Fin 2) (LaurentPolynomial R)), P.det=1 →
    ((P.transpose.map invert) * !![0,1;-1,0] * P = !![0,1;-1,0] ↔
      ∀ i j, invert (P i j)=P i j)) ∧
  (∀ (R : Type) [CommRing R] (f : LaurentPolynomial R),
    invert f=f ↔ ∃ p : R[X], Polynomial.eval₂ LaurentPolynomial.C laplacianVar p=f) ∧
  (∀ u v : Phase5, pairing5 (common5 u) (common5 v)=pairing5 u v) ∧
  (∀ (u v : Phase5) (ψ : Wave5) (x : Fin 5 → ZMod 3),
    weyl5 u (weyl5 v ψ) x=ZMod.stdAddChar (pairing5 u v)*weyl5 v (weyl5 u ψ) x) ∧
  pairing5 a0 a1=0 ∧ pairing5 (processed5 a0) (processed5 a1)=2 ∧
  (weylOp a0 * weylOp a1 = weylOp a1 * weylOp a0) ∧
  (weylOp (processed5 a0) * weylOp (processed5 a1) ≠
    weylOp (processed5 a1) * weylOp (processed5 a0)) ∧
  (¬ ∃ U : Wave5 ≃ₗ[ℂ] Wave5, ∀ u : Phase5,
      (U : Wave5 →ₗ[ℂ] Wave5) * weylOp u * (U.symm : Wave5 →ₗ[ℂ] Wave5) = weylOp (processed5 u))

/-- **GSC:fixed-word** (source-fixed canonical and Gauss-preserving scores). -/
@[ledger "GSC:fixed-word"]
def fixedWord : Prop :=
  ∀ (K : Canvas) (R : Type) [CommRing R] (w : List (Instruction K R))
    (s : FieldState K R) (φ : K.V → R) (u v : Tangent K R),
    run (w.reverse.map inverseInstruction) (run w s)=s ∧
    run w (run (w.reverse.map inverseInstruction) s)=s ∧
    (∀ n, defect (run (w.take n) s)=defect s) ∧
    run w (gauge φ s)=gauge φ (run w s) ∧
    run w (perturb s u)=perturb (run w s) (tangentRun w u) ∧
    omega (tangentRun w u) (tangentRun w v)=omega u v ∧
    K.div (tangentRun w u).2=K.div u.2

/-- **GSC:owned-compiler** (atomic local commits and the padded Maxwell cycle). -/
@[ledger "GSC:owned-compiler"]
def ownedCompiler : Prop :=
  ∀ (K : Canvas) (R : Type) [CommRing R] (w : List (Instruction K R)),
    (realizer w).WellPosed ∧
    (∀ (g : Instruction K R) (x : (frame K R).Table),
      (profile g).apply x=encode (execute g (decode x))) ∧
    (∀ (g : Instruction K R), (profile g).reads=reads g ∧ (profile g).writes=writes g) ∧
    (∀ s n, n ≤ w.length → history w s n=run (w.take n) s) ∧
    (∀ s, history w s (law w).score.period=run w s) ∧
    (∀ (J : K.E → R) s, run (maxwellWord K J) s=fieldTick J s) ∧
    (∀ (J : K.E → ZMod 8) (s : FieldState K (ZMod 8)), fieldTick J s =
      let t := maxwellTick K J ⟨s.A,s.E,s.ρ⟩; ⟨t.A,t.E,t.ρ⟩)

/-- **GSC:c8-receipts** (both actual half phases, their coefficients and phase obstruction). -/
@[ledger "GSC:c8-receipts"]
def c8Receipts : Prop :=
  (∀ x : C8, χ x=ZMod.stdAddChar x) ∧
  (∀ b s t, q b (s+t)=q b s*q b t*χ (-(s*t))) ∧
  (∀ b x, q b (-x)=q b x) ∧ (∀ b, q b 0=1) ∧
  (∀ b x, star (q b x)*q b x=1) ∧
  (q false 1 ≠ q true 1) ∧ (∀ b, (q b 1)^8 ≠ 1) ∧
  (∀ b x, q b x ∈ receiptRing) ∧ (∀ b a, kineticKernel b a ∈ receiptRing) ∧
  (∀ b, (kinetic b).conjTranspose * kinetic b=1) ∧
  (∀ b x y, (kinetic b).conjTranspose x y=star (kineticKernel b (-(x-y))))

/-- **GSC:coherent-compiler** (vacuum words with full raw inverses and actual coefficients). -/
@[ledger "GSC:coherent-compiler"]
def coherentCompiler : Prop :=
  ∀ (K : Canvas) (w : List (CoherentGate K × Bool)),
    (compile K w).conjTranspose * compile K w=1 ∧
    compile K w * (compile K w).conjTranspose=1 ∧
    compile K (w.reverse.map (invertLetter K))=(compile K w).conjTranspose ∧
    (∀ φ, Covariant K (K.diff φ) (compile K w)) ∧
    (∀ ψ, Vacuum K ψ → Vacuum K ((compile K w).mulVec ψ)) ∧
    (∀ x y, compile K w x y ∈ receiptRing) ∧
    (∀ e b x y, edgeMatrix K e b x y=kineticKernel b (x e-y e) *
      if (fun f : {f : K.E // f ≠ e} => x f)=(fun f : {f : K.E // f ≠ e} => y f) then 1 else 0) ∧
    (∀ b, compile K (vacuumWord K b)=
      ((Finset.univ.toList.reverse.map (fun e => edgeMatrix K e b)).prod) *
      Matrix.diagonal (fun x => ∏ p, q b (K.curl x p))) ∧
    (∀ e a x, (translationProfile K e a).guard x ∧
      (translationProfile K e a).reads={e} ∧ (translationProfile K e a).writes={e} ∧
      (translationProfile K e a).apply x=Function.update x e (x e+a) ∧
      ∀ b, edgeMatrix K e b ((translationProfile K e a).apply x) x=kineticKernel b a)

/-- **GSM:transverse** (actual periodic two-dimensional source binding). -/
@[ledger "GSM:transverse"]
def transverseBinding : Prop :=
  (∀ (R : Type) [CommRing R] (a : Fin 4 → R), torus.div (transverse a)=0 ∧
    torus.curlStar (torus.curl (transverse a))=transverse (lap a)) ∧
  (∀ (R : Type) [CommRing R] (s : Phase4 R), defect (embed s)=0) ∧
  (∀ (R : Type) [CommRing R], Function.Injective (embed : Phase4 R → FieldState torus R)) ∧
  (∀ (j : Fin 4 → ZMod 8) (s : Phase4 (ZMod 8)),
    maxwellTick torus (transverse j) ⟨(embed s).A,(embed s).E,(embed s).ρ⟩ =
      ⟨(embed (tick j s)).A,(embed (tick j s)).E,(embed (tick j s)).ρ⟩)

/-- **GSM:block-source** (direct even-odd blocking and the original output). -/
@[ledger "GSM:block-source"]
def blockedSource : Prop :=
  ∀ (R : Type) [CommRing R],
    (∀ s : Phase4 R, assemble (even s) (odd s)=s) ∧
    (∀ x z : Phase2 R, even (assemble x z)=x ∧ odd (assemble x z)=z) ∧
    (∀ (j : Fin 4 → R) (s : Phase4 R),
      even (tick j s)=localBlock (even s)+crossBlock (odd s)+evenForce j ∧
      odd (tick j s)=crossBlock (even s)+localBlock (odd s)+oddForce j) ∧
    (∀ (s : Phase4 R) (i : Fin 2), (coarseRead s).1 i=
      (s.1 (![0,2] i+1)-s.1 (![0,2] i))+
      (s.1 (![0,2] i+2)-s.1 (![0,2] i+1)))

/-- **GSM:forced-memory** (exact sources, hidden preparation and constructive reconstruction). -/
@[ledger "GSM:forced-memory"]
def forcedMemory : Prop :=
  ∀ (R : Type) [CommRing R],
    (∀ (j : ℕ → Fin 4 → R) (s : ℕ → Phase4 R),
      (∀ n, s (n+1)=tick (j n) (s n)) → ∀ n,
      even (s (n+1))=localBlock (even (s n))+crossBlock ((localBlock^n) (odd (s 0)))+
        (∑ r ∈ range n, crossBlock ((localBlock^(n-1-r)) (crossBlock (even (s r)))))+
        (∑ r ∈ range n, crossBlock ((localBlock^(n-1-r)) (oddForce (j r))))+evenForce (j n)) ∧
    (∀ (j : ℕ → Fin 4 → R) (x : ℕ → Phase2 R) z0 n,
      hidden j x z0 n=(localBlock^n) z0+
        (∑ r ∈ range n, (localBlock^(n-1-r)) (crossBlock (x r)))+
        (∑ r ∈ range n, (localBlock^(n-1-r)) (oddForce (j r)))) ∧
    (∀ (j : ℕ → Fin 4 → R) (x : ℕ → Phase2 R) z0,
      (∀ n, x (n+1)=localBlock (x n)+crossBlock (hidden j x z0 n)+evenForce (j n)) ↔
      (∀ n, assemble (x (n+1)) (hidden j x z0 (n+1))=
        tick (j n) (assemble (x n) (hidden j x z0 n)))) ∧
    (∀ (j : ℕ → Fin 4 → R) (s t : ℕ → Phase4 R),
      (∀ n, s (n+1)=tick (j n) (s n)) → (∀ n, t (n+1)=tick (j n) (t n)) →
      s 0=t 0 → ∀ n, s n=t n) ∧
    (∀ x : Phase2 R, (localBlock^4) x=x)

/-- **GSM:coarse-obstruction** (Gauss-valid native C8 nonautonomy). -/
@[ledger "GSM:coarse-obstruction"]
def coarseObstruction : Prop :=
  (coarseRead zeroFine=(0,0) ∧ coarseRead oddFine=(0,0) ∧
    coarseRead (tick 0 zeroFine)=(0,0) ∧ coarseRead (tick 0 oddFine)=(0,![7,7])) ∧
  coarseRead zeroFine=coarseRead oddFine ∧
  coarseRead (tick 0 zeroFine) ≠ coarseRead (tick 0 oddFine) ∧
  defect (embed zeroFine)=0 ∧ defect (embed oddFine)=0 ∧
  ¬ ∃ U : Phase2 (ZMod 8) → Phase2 (ZMod 8), ∀ s, coarseRead (tick 0 s)=U (coarseRead s)

end Artform.Scores.Gauge.Statement
