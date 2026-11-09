import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CGUpperCoordinateLocalInverse

/-! F10CH: regularity of the accepted parameter-space inverse and local word injectivity.
All injectivity statements retain the accepted source-neighborhood restriction.
Source Spin coverage, source local kernel control and subgroup charts remain separate.
Candidate until complete strict compilation and independent audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open scoped ContDiff Matrix.Norms.Elementwise

theorem source9OrderedUpperCoordinateLocalHomeomorph_symm_zero :
    source9OrderedUpperCoordinateLocalHomeomorph.symm (0 : Fin 36 → ℝ) = 0 := by
  have h := source9OrderedUpperCoordinateLocalHomeomorph_left_inv 0
    source9OrderedUpperCoordinateLocalHomeomorph_zero_mem_source
  rw [source9OrderedUpperCoordinateMap_zero] at h
  exact h

/-- The accepted inverse has the literal identity strict derivative at zero. -/
theorem source9OrderedUpperCoordinateLocalHomeomorph_symm_hasStrictFDerivAt_zero :
    HasStrictFDerivAt source9OrderedUpperCoordinateLocalHomeomorph.symm
      (ContinuousLinearMap.id ℝ (Fin 36 → ℝ)) 0 := by
  have h := source9OrderedUpperCoordinateMap_hasStrictFDerivAt_refl.to_localInverse
    (f' := ContinuousLinearEquiv.refl ℝ (Fin 36 → ℝ))
  have heq :
      source9OrderedUpperCoordinateMap_hasStrictFDerivAt_refl.localInverse
        source9OrderedUpperCoordinateMap (ContinuousLinearEquiv.refl ℝ (Fin 36 → ℝ)) 0 =
      (source9OrderedUpperCoordinateLocalHomeomorph.symm :
        (Fin 36 → ℝ) → (Fin 36 → ℝ)) := rfl
  have hid : ((ContinuousLinearEquiv.refl ℝ (Fin 36 → ℝ)).symm :
      (Fin 36 → ℝ) →L[ℝ] (Fin 36 → ℝ)) =
      ContinuousLinearMap.id ℝ (Fin 36 → ℝ) := rfl
  rw [heq, hid, source9OrderedUpperCoordinateMap_zero] at h
  exact h

theorem source9OrderedUpperCoordinateLocalHomeomorph_symm_hasFDerivAt_zero :
    HasFDerivAt source9OrderedUpperCoordinateLocalHomeomorph.symm
      (ContinuousLinearMap.id ℝ (Fin 36 → ℝ)) 0 :=
  source9OrderedUpperCoordinateLocalHomeomorph_symm_hasStrictFDerivAt_zero.hasFDerivAt

theorem source9OrderedUpperCoordinateLocalHomeomorph_symm_fderiv_zero :
    fderiv ℝ source9OrderedUpperCoordinateLocalHomeomorph.symm 0 =
      ContinuousLinearMap.id ℝ (Fin 36 → ℝ) :=
  source9OrderedUpperCoordinateLocalHomeomorph_symm_hasFDerivAt_zero.fderiv

/-- Every-order regularity at zero of the same accepted inverse, including analytic order. -/
theorem source9OrderedUpperCoordinateLocalHomeomorph_symm_contDiffAt_zero (n : ℕ∞ω) :
    ContDiffAt ℝ n source9OrderedUpperCoordinateLocalHomeomorph.symm 0 := by
  apply source9OrderedUpperCoordinateLocalHomeomorph.contDiffAt_symm
    (f₀' := ContinuousLinearEquiv.refl ℝ (Fin 36 → ℝ))
    source9OrderedUpperCoordinateLocalHomeomorph_zero_mem_target
  · rw [source9OrderedUpperCoordinateLocalHomeomorph_coe,
      source9OrderedUpperCoordinateLocalHomeomorph_symm_zero]
    exact source9OrderedUpperCoordinateMap_hasFDerivAt_zero
  · rw [source9OrderedUpperCoordinateLocalHomeomorph_coe,
      source9OrderedUpperCoordinateLocalHomeomorph_symm_zero]
    exact (source9OrderedUpperCoordinateMap_contDiff n).contDiffAt

/-- The actual upper coordinates distinguish parameters on the accepted source neighborhood. -/
theorem source9OrderedUpperCoordinateMap_injOn_source :
    Set.InjOn source9OrderedUpperCoordinateMap
      source9OrderedUpperCoordinateLocalHomeomorph.source := by
  intro t ht u hu h
  calc
    t = source9OrderedUpperCoordinateLocalHomeomorph.symm
        (source9OrderedUpperCoordinateMap t) :=
      (source9OrderedUpperCoordinateLocalHomeomorph_left_inv t ht).symm
    _ = source9OrderedUpperCoordinateLocalHomeomorph.symm
        (source9OrderedUpperCoordinateMap u) :=
      congrArg (fun y : Fin 36 → ℝ => source9OrderedUpperCoordinateLocalHomeomorph.symm y) h
    _ = u := source9OrderedUpperCoordinateLocalHomeomorph_left_inv u hu

/-- The entire actual natural matrix image also distinguishes parameters on that neighborhood. -/
theorem source9OrderedStrictPlaneWord_matrix_injOn_source :
    Set.InjOn (fun t : Fin 36 → ℝ =>
      ((source9SpinVectorOrthogonalHom (source9OrderedStrictPlaneWord t)) :
        Matrix SpaceIndex SpaceIndex ℝ))
      source9OrderedUpperCoordinateLocalHomeomorph.source := by
  intro t ht u hu h
  apply source9OrderedUpperCoordinateMap_injOn_source ht hu
  change source9OrderedUpperProjection
      ((source9SpinVectorOrthogonalHom (source9OrderedStrictPlaneWord t)) :
        Matrix SpaceIndex SpaceIndex ℝ) =
    source9OrderedUpperProjection
      ((source9SpinVectorOrthogonalHom (source9OrderedStrictPlaneWord u)) :
        Matrix SpaceIndex SpaceIndex ℝ)
  exact congrArg source9OrderedUpperProjection h

/-- The original source group word is locally injective on the established parameter set. -/
theorem source9OrderedStrictPlaneWord_injOn_source :
    Set.InjOn source9OrderedStrictPlaneWord
      source9OrderedUpperCoordinateLocalHomeomorph.source := by
  intro t ht u hu h
  apply source9OrderedStrictPlaneWord_matrix_injOn_source ht hu
  exact congrArg (fun g : spinGroup source9Quadratic =>
    ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ)) h

#print axioms source9OrderedUpperCoordinateLocalHomeomorph_symm_zero
#print axioms source9OrderedUpperCoordinateLocalHomeomorph_symm_hasStrictFDerivAt_zero
#print axioms source9OrderedUpperCoordinateLocalHomeomorph_symm_hasFDerivAt_zero
#print axioms source9OrderedUpperCoordinateLocalHomeomorph_symm_fderiv_zero
#print axioms source9OrderedUpperCoordinateLocalHomeomorph_symm_contDiffAt_zero
#print axioms source9OrderedUpperCoordinateMap_injOn_source
#print axioms source9OrderedStrictPlaneWord_matrix_injOn_source
#print axioms source9OrderedStrictPlaneWord_injOn_source
end
end FCP.BFSSPairedSpin9Clifford
