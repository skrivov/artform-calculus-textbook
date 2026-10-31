import ArtformScores.Gauge.Defs
import ArtformScores.GravityBridge.Memory
/-! # Native periodic source binding and exact forced coarse memory -/

set_option autoImplicit false
namespace Artform.Scores.Gauge
open Artform Finset
abbrev Vertex := Fin 4 × Fin 2
abbrev Link := Bool × Vertex

abbrev torus : Canvas where
  V := Vertex
  E := Link
  F := Vertex
  src := Prod.snd
  tgt e := if e.1 then (e.2.1, e.2.2 + 1) else (e.2.1 + 1, e.2.2)
  boundary p := [((false,p),true), ((true,(p.1+1,p.2)),true),
    ((false,(p.1,p.2+1)),false), ((true,p),false)]
  closed p := by
    simp [IsClosedWalk, List.isChain_cons_cons, stepStart, stepEnd]

variable {R : Type} [CommRing R]
abbrev Phase4 (R : Type) := (Fin 4 → R) × (Fin 4 → R)
def lap (a : Fin 4 → R) (i : Fin 4) : R :=
  2 * a i - a (i + 1) - a (i + 3)
def transverse (a : Fin 4 → R) : torus.E → R := fun e => if e.1 then a e.2.1 else 0

def embed (s : Phase4 R) : FieldState torus R := ⟨transverse s.1, transverse s.2, 0⟩
def tick (j : Fin 4 → R) (s : Phase4 R) : Phase4 R :=
  let ep := s.2 + lap s.1 - j
  (s.1 - ep, ep)

lemma transverse_add (a b : Fin 4 → R) : transverse (a+b) = transverse a + transverse b := by
  funext ⟨d,x,y⟩; cases d <;> simp [transverse]
lemma transverse_sub (a b : Fin 4 → R) : transverse (a-b) = transverse a - transverse b := by
  funext ⟨d,x,y⟩; cases d <;> simp [transverse]
lemma div_transverse (a : Fin 4 → R) : torus.div (transverse a) = 0 := by
  funext ⟨x,y⟩
  fin_cases x <;> fin_cases y <;>
    simp [Canvas.div, torus, transverse, Fintype.sum_prod_type, Fin.sum_univ_succ]

lemma curl_transverse (a : Fin 4 → R) (p : torus.F) :
    torus.curl (transverse a) p = a (p.1+1) - a p.1 := by
  rcases p with ⟨x,y⟩
  fin_cases x <;> fin_cases y <;>
    simp [Canvas.curl, Canvas.inc, torus, transverse, Fintype.sum_prod_type,
      Fin.sum_univ_succ] <;> ring

lemma curlStar_transverse (a : Fin 4 → R) :
    torus.curlStar (torus.curl (transverse a)) = transverse (lap a) := by
  funext ⟨d,x,y⟩
  cases d <;> fin_cases x <;> fin_cases y <;>
    simp [Canvas.curlStar, curl_transverse, Canvas.inc, torus, transverse, lap,
      Fintype.sum_prod_type, Fin.sum_univ_succ] <;> ring

lemma embed_injective : Function.Injective (embed : Phase4 R → FieldState torus R) := by
  intro s t h
  apply Prod.ext
  · funext i
    exact congrArg (fun u => u.A (true,i,0)) h
  · funext i
    exact congrArg (fun u => u.E (true,i,0)) h

lemma native_transverse (j : Fin 4 → ZMod 8) (s : Phase4 (ZMod 8)) :
    maxwellTick torus (transverse j) ⟨(embed s).A,(embed s).E,(embed s).ρ⟩ =
      ⟨(embed (tick j s)).A,(embed (tick j s)).E,(embed (tick j s)).ρ⟩ := by
  have hE : transverse s.2 + torus.curlStar (torus.curl (transverse s.1)) - transverse j =
      transverse (s.2 + lap s.1 - j) := by
    rw [curlStar_transverse, transverse_sub, transverse_add]
  unfold maxwellTick
  simp only [embed, hE, div_transverse, sub_zero, tick, transverse_sub]

abbrev Phase2 (R : Type) := (Fin 2 → R) × (Fin 2 → R)
def even (s : Phase4 R) : Phase2 R := (fun i => s.1 (![0,2] i), fun i => s.2 (![0,2] i))
def odd (s : Phase4 R) : Phase2 R := (fun i => s.1 (![1,3] i), fun i => s.2 (![1,3] i))
def assemble (x z : Phase2 R) : Phase4 R :=
  (![x.1 0,z.1 0,x.1 1,z.1 1], ![x.2 0,z.2 0,x.2 1,z.2 1])

omit [CommRing R] in
lemma assemble_reads (s : Phase4 R) : assemble (even s) (odd s) = s := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
omit [CommRing R] in
lemma read_assemble (x z : Phase2 R) : even (assemble x z) = x ∧ odd (assemble x z) = z := by
  constructor <;> apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

def localBlock : Phase2 R →ₗ[R] Phase2 R where
  toFun x := (-x.1-x.2, (fun i => 2*x.1 i+x.2 i))
  map_add' x y := by apply Prod.ext <;> funext i <;> simp <;> ring
  map_smul' r x := by apply Prod.ext <;> funext i <;> simp <;> ring

def crossBlock : Phase2 R →ₗ[R] Phase2 R where
  toFun x := (fun i => x.1 i+x.1 (i+1), fun i => -(x.1 i+x.1 (i+1)))
  map_add' x y := by apply Prod.ext <;> funext i <;> simp <;> ring
  map_smul' r x := by apply Prod.ext <;> funext i <;> simp <;> ring

def evenForce (j : Fin 4 → R) : Phase2 R := (fun i => j (![0,2] i), fun i => -j (![0,2] i))
def oddForce (j : Fin 4 → R) : Phase2 R := (fun i => j (![1,3] i), fun i => -j (![1,3] i))

lemma blocked_tick (j : Fin 4 → R) (s : Phase4 R) :
    even (tick j s) = localBlock (even s) + crossBlock (odd s) + evenForce j ∧
    odd (tick j s) = crossBlock (even s) + localBlock (odd s) + oddForce j := by
  constructor <;> apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [tick, lap, even, odd, localBlock, crossBlock, evenForce, oddForce] <;> ring

lemma block_square (x : Phase2 R) : (localBlock ^ 2) x = -x := by
  apply Prod.ext <;> funext i <;> simp [pow_two, Module.End.mul_apply, localBlock] <;> ring
lemma block_period (x : Phase2 R) : (localBlock ^ 4) x = x := by
  have h : (4 : ℕ) = 2+2 := rfl
  rw [h, pow_add, Module.End.mul_apply, block_square, block_square, neg_neg]

lemma sourced_memory (j : ℕ → Fin 4 → R) (s : ℕ → Phase4 R)
    (hs : ∀ n, s (n + 1) = tick (j n) (s n)) (n : ℕ) :
    even (s (n+1)) = localBlock (even (s n)) +
      crossBlock ((localBlock ^ n) (odd (s 0))) +
      (∑ r ∈ range n, crossBlock ((localBlock ^ (n-1-r)) (crossBlock (even (s r))))) +
      (∑ r ∈ range n, crossBlock ((localBlock ^ (n-1-r)) (oddForce (j r)))) +
      evenForce (j n) := by
  have hz : ∀ r, odd (s (r+1)) =
      (crossBlock (even (s r)) + oddForce (j r)) + localBlock (odd (s r)) := by
    intro r
    rw [hs r, (blocked_tick (j r) (s r)).2]
    abel
  have hm := GravityBridge.forced_memory localBlock
    (fun r => crossBlock (even (s r)) + oddForce (j r)) (fun r => odd (s r)) hz n
  rw [hs n, (blocked_tick (j n) (s n)).1, hm]
  simp only [map_add, map_sum, Finset.sum_add_distrib]
  abel

def output (x : Phase2 R) : Phase2 R := (fun i => x.1 (i+1)-x.1 i, x.2)
def coarseRead (s : Phase4 R) : Phase2 R := output (even s)
lemma curvature_output (s : Phase4 R) (i : Fin 2) :
    (coarseRead s).1 i =
      (s.1 (![0,2] i + 1)-s.1 (![0,2] i)) +
      (s.1 (![0,2] i + 2)-s.1 (![0,2] i + 1)) := by
  fin_cases i <;> simp [coarseRead, output, even]

def zeroFine : Phase4 (ZMod 8) := (0,0)
def oddFine : Phase4 (ZMod 8) := (![0,1,0,0],0)
lemma coarse_initial : coarseRead zeroFine = coarseRead oddFine := by decide +kernel
lemma coarse_next : coarseRead (tick 0 zeroFine) ≠ coarseRead (tick 0 oddFine) := by decide +kernel
lemma coarse_not_autonomous :
    ¬ ∃ U : Phase2 (ZMod 8) → Phase2 (ZMod 8),
      ∀ s, coarseRead (tick 0 s) = U (coarseRead s) := by
  rintro ⟨U,h⟩
  apply coarse_next
  rw [h zeroFine, h oddFine, coarse_initial]

def hidden (j : ℕ → Fin 4 → R) (x : ℕ → Phase2 R) (z0 : Phase2 R) : ℕ → Phase2 R
  | 0 => z0
  | n+1 => crossBlock (x n)+localBlock (hidden j x z0 n)+oddForce (j n)
lemma hidden_formula (j : ℕ → Fin 4 → R) (x : ℕ → Phase2 R) (z0 : Phase2 R) (n : ℕ) :
    hidden j x z0 n = (localBlock^n) z0 +
      (∑ r ∈ range n, (localBlock^(n-1-r)) (crossBlock (x r))) +
      (∑ r ∈ range n, (localBlock^(n-1-r)) (oddForce (j r))) := by
  have hz : ∀ r, hidden j x z0 (r+1) =
      (crossBlock (x r)+oddForce (j r))+localBlock (hidden j x z0 r) := by
    intro r; rw [hidden]; abel
  rw [GravityBridge.forced_memory localBlock _ _ hz n]
  simp only [hidden, map_add, Finset.sum_add_distrib]
  abel

lemma reconstruction_iff (j : ℕ → Fin 4 → R) (x : ℕ → Phase2 R) (z0 : Phase2 R) :
    (∀ n, x (n + 1) = localBlock (x n)+crossBlock (hidden j x z0 n)+evenForce (j n)) ↔
    (∀ n, assemble (x (n+1)) (hidden j x z0 (n+1)) =
      tick (j n) (assemble (x n) (hidden j x z0 n))) := by
  constructor
  · intro hx n
    have hb := blocked_tick (j n) (assemble (x n) (hidden j x z0 n))
    rw [(read_assemble _ _).1, (read_assemble _ _).2] at hb
    calc
      _ = assemble (even (tick (j n) (assemble (x n) (hidden j x z0 n))))
          (odd (tick (j n) (assemble (x n) (hidden j x z0 n)))) := by
        rw [hb.1, hb.2, hx n, hidden]
      _ = _ := assemble_reads _
  · intro hs n
    have hb := (blocked_tick (j n) (assemble (x n) (hidden j x z0 n))).1
    rw [← hs n, (read_assemble _ _).1, (read_assemble _ _).1,
      (read_assemble _ _).2] at hb
    exact hb

lemma trajectory_unique (j : ℕ → Fin 4 → R) (s t : ℕ → Phase4 R)
    (hs : ∀ n, s (n + 1) = tick (j n) (s n)) (ht : ∀ n, t (n + 1) = tick (j n) (t n))
    (h0 : s 0 = t 0) : ∀ n, s n=t n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => rw [hs,ht,ih]

lemma embed_gauss (s : Phase4 R) : defect (embed s)=0 := by
  simp [defect, embed, div_transverse]

lemma coarse_values : coarseRead zeroFine=(0,0) ∧ coarseRead oddFine=(0,0) ∧
    coarseRead (tick 0 zeroFine)=(0,0) ∧
    coarseRead (tick 0 oddFine)=(0,![7,7]) := by decide +kernel

end Artform.Scores.Gauge
