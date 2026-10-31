import ArtformScores.Nonabelian.OrbitData

/-! # The complete physical orbit carrier and its weighted inclusion -/
set_option autoImplicit false
namespace Artform.Scores.Nonabelian
open Finset
lemma orbit_gauge : ∀ h x, orbitIndex (gauge h x)=orbitIndex x := by decide +kernel
lemma orbit_representative : ∀ i, orbitIndex (representative i)=i := by decide +kernel
lemma orbit_reaches : ∀ x, ∃ h, gauge h (representative (orbitIndex x))=x := by
  decide +kernel
lemma orbit_iff : ∀ x y, orbitIndex x=orbitIndex y ↔ ∃ h, gauge h x=y := by
  decide +kernel
lemma orbit_weight_count : ∀ i,
    (Finset.univ.filter (fun x => orbitIndex x=i)).card=orbitWeight i := by decide +kernel
lemma orbit_weight_pos (i : Fin 11) : 0 < orbitWeight i := by fin_cases i <;> decide

abbrev orbitSetoid : Setoid Raw := Setoid.ker orbitIndex
abbrev Physical := Quotient orbitSetoid
def physicalEquiv : Physical ≃ Fin 11 where
  toFun := Quotient.lift orbitIndex (fun _ _ h => h)
  invFun i := ⟦representative i⟧
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h x => exact Quotient.sound (orbit_representative (orbitIndex x))
  right_inv := orbit_representative
noncomputable instance : Fintype Physical := Fintype.ofEquiv (Fin 11) physicalEquiv.symm
lemma physical_card : Fintype.card Physical=11 := by
  rw [Fintype.card_congr physicalEquiv,Fintype.card_fin]

def Vacuum {R : Type} (ψ : Raw → R) : Prop := ∀ h x, ψ (gauge h x)=ψ x
def orbitInclude {R : Type} (v : Fin 11 → R) : Raw → R := fun x => v (orbitIndex x)
def orbitRead {R : Type} (ψ : Raw → R) : Fin 11 → R := fun i => ψ (representative i)
lemma read_orbitInclude {R : Type} (v : Fin 11 → R) : orbitRead (orbitInclude v)=v := by
  funext i
  simp [orbitRead,orbitInclude,orbit_representative]
lemma orbitInclude_vacuum {R : Type} (v : Fin 11 → R) : Vacuum (orbitInclude v) := by
  intro h x
  simp [orbitInclude,orbit_gauge]
lemma vacuum_complete {R : Type} (ψ : Raw → R) : Vacuum ψ ↔ orbitInclude (orbitRead ψ)=ψ := by
  constructor
  · intro h
    funext x
    obtain ⟨g,hg⟩ := orbit_reaches x
    exact (h g (representative (orbitIndex x))).symm.trans (congrArg ψ hg)
  · intro h
    rw [← h]
    exact orbitInclude_vacuum _

lemma sum_orbits {R : Type} [AddCommMonoid R] (f : Fin 11 → R) :
    ∑ x : Raw, f (orbitIndex x)=∑ i, orbitWeight i • f i := by
  have h (x : Raw) : f (orbitIndex x)=∑ i : Fin 11, if orbitIndex x=i then f i else 0 := by
    simp
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,orbit_weight_count]

lemma weighted_pairing {R : Type} [CommRing R] (u v : Fin 11 → R) :
    ∑ x, orbitInclude u x*orbitInclude v x=∑ i, (orbitWeight i : R)*u i*v i := by
  simpa only [orbitInclude,nsmul_eq_mul,mul_assoc] using sum_orbits (fun i => u i*v i)

/-! ## Non-vacuity -/
example : representative 1=(1,Equiv.swap 0 1) := by decide +kernel
example : orbitWeight 1=3 := rfl
example : Vacuum (orbitInclude (Pi.single 1 (1:ℚ))) := orbitInclude_vacuum _
end Artform.Scores.Nonabelian
