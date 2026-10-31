import ArtformScores.GravityBridge.Native.Full40.Quadratic
/-! # The original full coordinate force from the complete quadratic action -/
namespace Artform.Scores.GravityBridge.Native.Full40
variable {X K : Type*} [AddCommGroup X] [Field K] [CharZero K]
noncomputable def firstVariationMap [Fintype X] (d : Fin 4 → X) (kappa : K)
    (q : NativeField X K) : NativeField X K →ₗ[K] K where
  toFun p := nativeFirstVariation d kappa q p
  map_add' p t := by
    simp only [nativeFirstVariation, native_bilinear_add_left, native_bilinear_add_right]
    ring
  map_smul' c p := by
    simp only [nativeFirstVariation, native_bilinear_smul_left, native_bilinear_smul_right,
      RingHom.id_apply, smul_eq_mul]
    ring
noncomputable def fieldCoordinates : NativeField X K ≃ₗ[K] (X × Coordinate → K) where
  toFun q := fun xa => pack (q xa.1) xa.2
  invFun c := fun x => unpack (fun a => c (x, a))
  left_inv q := by
    funext x
    exact unpack_pack (q x)
  right_inv c := by
    funext xa
    exact congrFun (pack_unpack (fun a => c (xa.1, a))) xa.2
  map_add' q p := by
    funext xa
    rcases xa with ⟨x, a⟩
    cases a <;> rfl
  map_smul' c q := by
    funext xa
    rcases xa with ⟨x, a⟩
    cases a <;> rfl
noncomputable def fullForce [Fintype X] (d : Fin 4 → X) (kappa : K)
    (q : NativeField X K) : X × Coordinate → K := by
  classical
  exact fun a => firstVariationMap d kappa q
    (fieldCoordinates.symm (Pi.single a 1))
noncomputable def fullJacobian [Fintype X] (d : Fin 4 → X) (kappa : K) :
    Matrix (X × Coordinate) (X × Coordinate) K := by
  classical
  exact fun a b => fullForce d kappa (fieldCoordinates.symm (Pi.single b 1)) a
def directFirstVariation [Fintype X] (d : Fin 4 → X) (kappa : K)
    (q p : NativeField X K) : K :=
  ∑ x, ((∑ r, (bivPair (nativeLU d p x r) (internalStar (nativeK d q x r)) +
    bivPair (nativeLU d q x r) (internalStar (nativeK d p x r)) +
    bivPair (flatComplement r)
      (internalStar (rawPlaquetteContact d q p x r + rawPlaquetteContact d p q x r)))) +
    (2 * kappa) * (∑ r, eta (faceFirst r) * eta (faceSecond r) *
      etaPair (nativeTheta d q x r) (nativeTheta d p x r)))
end Artform.Scores.GravityBridge.Native.Full40
