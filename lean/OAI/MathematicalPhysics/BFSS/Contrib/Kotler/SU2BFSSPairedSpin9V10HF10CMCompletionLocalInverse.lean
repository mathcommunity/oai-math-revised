import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CLCompletionSmoothStrictDerivative
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! F10CM: local inversion of the accepted completion map on the original full matrix space.
Both inverse laws and injectivity retain the constructed source/target membership conditions.
Global injectivity, source Spin fiber control and source neighborhood coverage are not asserted.
Candidate until complete strict compilation and independent audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open scoped Matrix.Norms.Elementwise

theorem source9OrthogonalCompletionMap_hasStrictFDerivAt_refl :
    HasStrictFDerivAt source9OrthogonalCompletionMap
      ((ContinuousLinearEquiv.refl ℝ (Matrix SpaceIndex SpaceIndex ℝ)) :
        Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] Matrix SpaceIndex SpaceIndex ℝ) 0 :=
  source9OrthogonalCompletionMap_hasStrictFDerivAt_zero

/-- The same accepted completion function, locally inverted by the pinned strict constructor. -/
noncomputable def source9OrthogonalCompletionLocalHomeomorph :
    OpenPartialHomeomorph (Matrix SpaceIndex SpaceIndex ℝ) (Matrix SpaceIndex SpaceIndex ℝ) :=
  source9OrthogonalCompletionMap_hasStrictFDerivAt_refl.toOpenPartialHomeomorph
    (f' := ContinuousLinearEquiv.refl ℝ (Matrix SpaceIndex SpaceIndex ℝ)) source9OrthogonalCompletionMap

theorem source9OrthogonalCompletionLocalHomeomorph_coe :
    (source9OrthogonalCompletionLocalHomeomorph :
      Matrix SpaceIndex SpaceIndex ℝ → Matrix SpaceIndex SpaceIndex ℝ) =
        source9OrthogonalCompletionMap :=
  source9OrthogonalCompletionMap_hasStrictFDerivAt_refl.toOpenPartialHomeomorph_coe
    (f' := ContinuousLinearEquiv.refl ℝ (Matrix SpaceIndex SpaceIndex ℝ))

theorem source9OrthogonalCompletionLocalHomeomorph_zero_mem_source :
    (0 : Matrix SpaceIndex SpaceIndex ℝ) ∈ source9OrthogonalCompletionLocalHomeomorph.source :=
  source9OrthogonalCompletionMap_hasStrictFDerivAt_refl.mem_toOpenPartialHomeomorph_source
    (f' := ContinuousLinearEquiv.refl ℝ (Matrix SpaceIndex SpaceIndex ℝ))

theorem source9OrthogonalCompletionLocalHomeomorph_zero_mem_target :
    (0 : Matrix SpaceIndex SpaceIndex ℝ) ∈ source9OrthogonalCompletionLocalHomeomorph.target := by
  have h : source9OrthogonalCompletionMap (0 : Matrix SpaceIndex SpaceIndex ℝ) ∈
      source9OrthogonalCompletionLocalHomeomorph.target :=
    source9OrthogonalCompletionMap_hasStrictFDerivAt_refl.image_mem_toOpenPartialHomeomorph_target
      (f' := ContinuousLinearEquiv.refl ℝ (Matrix SpaceIndex SpaceIndex ℝ))
  rw [source9OrthogonalCompletionMap_zero] at h
  exact h

theorem source9OrthogonalCompletionLocalHomeomorph_left_inv
    (B : Matrix SpaceIndex SpaceIndex ℝ) (hB : B ∈ source9OrthogonalCompletionLocalHomeomorph.source) :
    source9OrthogonalCompletionLocalHomeomorph.symm (source9OrthogonalCompletionMap B) = B := by
  have heq := congrFun source9OrthogonalCompletionLocalHomeomorph_coe B
  have h := source9OrthogonalCompletionLocalHomeomorph.left_inv hB
  exact (congrArg (fun Y : Matrix SpaceIndex SpaceIndex ℝ =>
    source9OrthogonalCompletionLocalHomeomorph.symm Y) heq).symm.trans h

theorem source9OrthogonalCompletionLocalHomeomorph_right_inv
    (Y : Matrix SpaceIndex SpaceIndex ℝ) (hY : Y ∈ source9OrthogonalCompletionLocalHomeomorph.target) :
    source9OrthogonalCompletionMap (source9OrthogonalCompletionLocalHomeomorph.symm Y) = Y := by
  have heq := congrFun source9OrthogonalCompletionLocalHomeomorph_coe
    (source9OrthogonalCompletionLocalHomeomorph.symm Y)
  exact heq.symm.trans (source9OrthogonalCompletionLocalHomeomorph.right_inv hY)

/-- Local ambient injectivity retains both matrices' membership in the accepted source set. -/
theorem source9OrthogonalCompletionMap_injOn_source :
    Set.InjOn source9OrthogonalCompletionMap source9OrthogonalCompletionLocalHomeomorph.source := by
  intro A hA B hB h
  calc
    A = source9OrthogonalCompletionLocalHomeomorph.symm (source9OrthogonalCompletionMap A) :=
      (source9OrthogonalCompletionLocalHomeomorph_left_inv A hA).symm
    _ = source9OrthogonalCompletionLocalHomeomorph.symm (source9OrthogonalCompletionMap B) :=
      congrArg (fun Y : Matrix SpaceIndex SpaceIndex ℝ =>
        source9OrthogonalCompletionLocalHomeomorph.symm Y) h
    _ = B := source9OrthogonalCompletionLocalHomeomorph_left_inv B hB

#print axioms source9OrthogonalCompletionMap_hasStrictFDerivAt_refl
#print axioms source9OrthogonalCompletionLocalHomeomorph
#print axioms source9OrthogonalCompletionLocalHomeomorph_coe
#print axioms source9OrthogonalCompletionLocalHomeomorph_zero_mem_source
#print axioms source9OrthogonalCompletionLocalHomeomorph_zero_mem_target
#print axioms source9OrthogonalCompletionLocalHomeomorph_left_inv
#print axioms source9OrthogonalCompletionLocalHomeomorph_right_inv
#print axioms source9OrthogonalCompletionMap_injOn_source
end
end FCP.BFSSPairedSpin9Clifford
