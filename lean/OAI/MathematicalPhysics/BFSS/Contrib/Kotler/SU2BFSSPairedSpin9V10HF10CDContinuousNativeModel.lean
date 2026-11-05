import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CCOrderedDerivativeNativeModel
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.Lie.OfAssociative

/-! F10CD: promote the accepted canonical model using standard topologies.
No new topology or norm instance is installed. This supplies no subgroup atlas,
source local kernel theorem, tangent identification or manifold differential.
Candidate until strict source and independent topology/type/axiom audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open scoped Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

-- Derive compatibility with the existing topology through the canonical submodule view.
local instance f10cdNativeSkewIsTopologicalAddGroup :
    IsTopologicalAddGroup (LieAlgebra.Orthogonal.so SpaceIndex ℝ) :=
  inferInstanceAs (IsTopologicalAddGroup
    ↥((LieAlgebra.Orthogonal.so SpaceIndex ℝ).toSubmodule))

local instance f10cdNativeSkewContinuousSMul :
    ContinuousSMul ℝ (LieAlgebra.Orthogonal.so SpaceIndex ℝ) :=
  inferInstanceAs (ContinuousSMul ℝ
    ↥((LieAlgebra.Orthogonal.so SpaceIndex ℝ).toSubmodule))

/-- Canonical skew matrices retain the topology induced by original matrix entries. -/
theorem source9NativeSkewTopology_induced :
    (inferInstance : TopologicalSpace (LieAlgebra.Orthogonal.so SpaceIndex ℝ)) =
      TopologicalSpace.induced
        (fun A : LieAlgebra.Orthogonal.so SpaceIndex ℝ => A.val)
        (inferInstance : TopologicalSpace (Matrix SpaceIndex SpaceIndex ℝ)) := rfl

/-- The same accepted model, promoted by finite-dimensional continuity. -/
noncomputable def source9OrderedStrictPlaneModelContinuousEquiv :
    (Fin 36 → ℝ) ≃L[ℝ] LieAlgebra.Orthogonal.so SpaceIndex ℝ :=
  source9OrderedStrictPlaneModelEquiv.toContinuousLinearEquiv

/-- The underlying linear equivalence is literally the qualified CC map. -/
theorem source9OrderedStrictPlaneModelContinuousEquiv_toLinearEquiv :
    source9OrderedStrictPlaneModelContinuousEquiv.toLinearEquiv =
      source9OrderedStrictPlaneModelEquiv := rfl

theorem source9OrderedStrictPlaneModelContinuousEquiv_continuous :
    Continuous source9OrderedStrictPlaneModelContinuousEquiv :=
  source9OrderedStrictPlaneModelContinuousEquiv.continuous

theorem source9OrderedStrictPlaneModelContinuousEquiv_symm_continuous :
    Continuous source9OrderedStrictPlaneModelContinuousEquiv.symm :=
  source9OrderedStrictPlaneModelContinuousEquiv.symm.continuous

/-- The actual ambient matrix derivative is the underlying matrix of this continuous model. -/
theorem source9OrderedStrictPlaneWord_matrix_fderiv_zero_continuousModel (v : Fin 36 → ℝ) :
    (fderiv ℝ (fun t : Fin 36 → ℝ =>
      ((source9SpinVectorOrthogonalHom (source9OrderedStrictPlaneWord t)) :
        Matrix SpaceIndex SpaceIndex ℝ)) 0) v =
      (source9OrderedStrictPlaneModelContinuousEquiv v : Matrix SpaceIndex SpaceIndex ℝ) :=
  source9OrderedStrictPlaneWord_matrix_fderiv_zero_model v

/-- The inverse still extracts the original enumerated upper matrix coordinates. -/
theorem source9OrderedStrictPlaneModelContinuousEquiv_symm_apply
    (A : LieAlgebra.Orthogonal.so SpaceIndex ℝ) (i : Fin 36) :
    source9OrderedStrictPlaneModelContinuousEquiv.symm A i =
      A.val (source9StrictPlaneRow i) (source9StrictPlaneColumn i) := by
  have hmodel : source9OrderedStrictPlaneModelEquiv
      (source9OrderedStrictPlaneModelContinuousEquiv.symm A) = A :=
    source9OrderedStrictPlaneModelContinuousEquiv.apply_symm_apply A
  have hmatrix := congrArg
    (fun B : LieAlgebra.Orthogonal.so SpaceIndex ℝ => B.val) hmodel
  have hderiv :=
    (source9OrderedStrictPlaneWord_matrix_fderiv_zero_model
      (source9OrderedStrictPlaneModelContinuousEquiv.symm A)).trans hmatrix
  have hentry := congrArg (fun M : Matrix SpaceIndex SpaceIndex ℝ =>
    M (source9StrictPlaneRow i) (source9StrictPlaneColumn i)) hderiv
  exact (source9OrderedStrictPlaneWord_matrix_fderiv_zero_upper
    (source9OrderedStrictPlaneModelContinuousEquiv.symm A) i).symm.trans hentry

#print axioms source9NativeSkewTopology_induced
#print axioms source9OrderedStrictPlaneModelContinuousEquiv
#print axioms source9OrderedStrictPlaneModelContinuousEquiv_toLinearEquiv
#print axioms source9OrderedStrictPlaneModelContinuousEquiv_continuous
#print axioms source9OrderedStrictPlaneModelContinuousEquiv_symm_continuous
#print axioms source9OrderedStrictPlaneWord_matrix_fderiv_zero_continuousModel
#print axioms source9OrderedStrictPlaneModelContinuousEquiv_symm_apply
end
end FCP.BFSSPairedSpin9Clifford
