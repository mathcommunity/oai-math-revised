import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CXIdentityChartInverseCliffordDerivative
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Equiv

/-! F10CY: the exact identity-chart derivative range is the span of native half-bivectors.
Use the qualified literal derivative, increasing original spatial pairs and accepted native skew
model. The resulting equivalences are real-linear and concern the actual ambient derivative range.
No source tangent-space identification, Lie-bracket compatibility, manifold or group-map
manifold differential is asserted. Candidate until strict compilation and independent audit. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open scoped Matrix.Norms.Elementwise

local instance f10cyLocalNormedAddCommGroup :
    NormedAddCommGroup (CliffordAlgebra source9Quadratic) := source9PBWNormedAddCommGroup
local instance f10cyLocalNormedSpace :
    NormedSpace ℝ (CliffordAlgebra source9Quadratic) := source9PBWNormedSpace

/-- The already qualified derivative of the literal actual chart inverse. -/
noncomputable def source9IdentityChartDerivative :
    (Fin 36 → ℝ) →L[ℝ] CliffordAlgebra source9Quadratic :=
  fderiv ℝ (fun t : Fin 36 → ℝ =>
    ((source9SpinIdentityLocalChart.symm t) : CliffordAlgebra source9Quadratic)) 0

/-- Its actual linear-map range in the original Clifford carrier. -/
noncomputable def source9IdentityChartDerivativeRange : Submodule ℝ (CliffordAlgebra source9Quadratic) :=
  LinearMap.range source9IdentityChartDerivative.toLinearMap

/-- Native increasing source pairs, independent of the chosen parameter enumeration. -/
noncomputable def source9NativeHalfBivectorSpan : Submodule ℝ (CliffordAlgebra source9Quadratic) :=
  Submodule.span ℝ (Set.range (fun p : source9StrictPlaneIndex =>
    (1 / 2 : ℝ) •
      (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector p.val.1) *
        CliffordAlgebra.ι source9Quadratic (source9CoordinateVector p.val.2))))

theorem source9IdentityChartDerivative_apply (v : Fin 36 → ℝ) :
    source9IdentityChartDerivative v =
      ((List.finRange 36).map (fun i => v i • ((1 / 2 : ℝ) •
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneRow i)) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneColumn i)))))).sum :=
  source9IdentityChartInverse_clifford_fderiv_zero_apply v

/-- Each exact coordinate direction maps to its positive original half-bivector. -/
theorem source9IdentityChartDerivative_coordinate (i : Fin 36) :
    source9IdentityChartDerivative (Pi.single i (1 : ℝ)) =
      (1 / 2 : ℝ) •
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneRow i)) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneColumn i))) := by
  have hvalue : source9IdentityChartDerivative (Pi.single i (1 : ℝ)) =
      ((List.finRange 36).map (fun j => (Pi.single i (1 : ℝ) : Fin 36 → ℝ) j • ((1 / 2 : ℝ) •
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneRow j)) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneColumn j)))))).sum :=
    source9IdentityChartDerivative_apply (Pi.single i (1 : ℝ))
  have hsum :
      ((List.finRange 36).map (fun j => (Pi.single i (1 : ℝ) : Fin 36 → ℝ) j • ((1 / 2 : ℝ) •
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneRow j)) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneColumn j)))))).sum =
        (1 / 2 : ℝ) •
          (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneRow i)) *
            CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneColumn i))) := by
    classical
    rw [← Fin.sum_univ_def]
    simp [Pi.single_apply]
  exact hvalue.trans hsum

/-- Both inclusions use the exact actual derivative and every original increasing native pair. -/
theorem source9IdentityChartDerivative_range_eq_halfBivectorSpan :
    source9IdentityChartDerivativeRange = source9NativeHalfBivectorSpan := by
  apply le_antisymm
  · change LinearMap.range source9IdentityChartDerivative.toLinearMap ≤ source9NativeHalfBivectorSpan
    rintro x ⟨v, rfl⟩
    change source9IdentityChartDerivative v ∈ source9NativeHalfBivectorSpan
    have hmem :
        ((List.finRange 36).map (fun i => v i • ((1 / 2 : ℝ) •
          (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneRow i)) *
            CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneColumn i)))))).sum ∈
          source9NativeHalfBivectorSpan := by
      rw [← Fin.sum_univ_def]
      apply source9NativeHalfBivectorSpan.sum_mem
      intro i _
      exact source9NativeHalfBivectorSpan.smul_mem (v i)
        (Submodule.subset_span ⟨source9StrictPlaneEnumeration i, rfl⟩)
    exact (source9IdentityChartDerivative_apply v).symm ▸ hmem
  · change Submodule.span ℝ (Set.range (fun p : source9StrictPlaneIndex =>
      (1 / 2 : ℝ) •
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector p.val.1) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector p.val.2)))) ≤
        source9IdentityChartDerivativeRange
    apply Submodule.span_le.2
    rintro x ⟨p, rfl⟩
    refine ⟨Pi.single (source9StrictPlaneEnumeration.symm p) (1 : ℝ), ?_⟩
    change source9IdentityChartDerivative (Pi.single (source9StrictPlaneEnumeration.symm p) (1 : ℝ)) = _
    have hp := source9StrictPlaneEnumeration.apply_symm_apply p
    have hr : source9StrictPlaneRow (source9StrictPlaneEnumeration.symm p) = p.val.1 :=
      congrArg (fun q : source9StrictPlaneIndex => q.val.1) hp
    have hc : source9StrictPlaneColumn (source9StrictPlaneEnumeration.symm p) = p.val.2 :=
      congrArg (fun q : source9StrictPlaneIndex => q.val.2) hp
    exact (source9IdentityChartDerivative_coordinate (source9StrictPlaneEnumeration.symm p)).trans
      (by rw [hr, hc])

/-- Parameters are linearly equivalent to this literal range by the qualified injective derivative. -/
noncomputable def source9IdentityChartDerivativeRangeEquiv :
    (Fin 36 → ℝ) ≃ₗ[ℝ] source9IdentityChartDerivativeRange :=
  LinearEquiv.ofInjective source9IdentityChartDerivative.toLinearMap
    source9IdentityChartInverse_clifford_fderiv_zero_injective

theorem source9IdentityChartDerivativeRangeEquiv_apply (v : Fin 36 → ℝ) :
    (source9IdentityChartDerivativeRangeEquiv v : CliffordAlgebra source9Quadratic) =
      source9IdentityChartDerivative v := rfl

/-- A real-linear equivalence with the existing canonical native skew space, without a bracket claim. -/
noncomputable def source9NativeSkewDerivativeRangeEquiv :
    LieAlgebra.Orthogonal.so SpaceIndex ℝ ≃ₗ[ℝ] source9IdentityChartDerivativeRange :=
  source9OrderedStrictPlaneModelEquiv.symm.trans source9IdentityChartDerivativeRangeEquiv

theorem source9NativeSkewDerivativeRangeEquiv_apply (A : LieAlgebra.Orthogonal.so SpaceIndex ℝ) :
    (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) =
      source9IdentityChartDerivative (source9OrderedStrictPlaneModelEquiv.symm A) := rfl

theorem source9NativeSkewDerivativeRangeEquiv_symm
    (x : source9IdentityChartDerivativeRange) :
    source9NativeSkewDerivativeRangeEquiv.symm x =
      source9OrderedStrictPlaneModelEquiv (source9IdentityChartDerivativeRangeEquiv.symm x) := rfl

/-- Every native matrix entry is the projected commutator of the corresponding actual range value. -/
theorem source9NativeSkewDerivativeRangeEquiv_projected_commutator
    (A : LieAlgebra.Orthogonal.so SpaceIndex ℝ) (i j : SpaceIndex) :
    source9CliffordVectorProjection
      ((source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector j) -
        CliffordAlgebra.ι source9Quadratic (source9CoordinateVector j) *
          (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic)) i = A.val i j := by
  let v : Fin 36 → ℝ := source9OrderedStrictPlaneModelEquiv.symm A
  have hvalue : (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) =
      (fderiv ℝ (fun t : Fin 36 → ℝ =>
        ((source9SpinIdentityLocalChart.symm t) : CliffordAlgebra source9Quadratic)) 0) v := rfl
  have hcomm : source9CliffordVectorProjection
      ((source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector j) -
        CliffordAlgebra.ι source9Quadratic (source9CoordinateVector j) *
          (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic)) i =
      source9PlaneWordVectorVelocity source9StrictPlaneRow source9StrictPlaneColumn
        (source9CoordinateVector j) (List.finRange 36) v i :=
    (congrArg (fun a : CliffordAlgebra source9Quadratic =>
      source9CliffordVectorProjection
        (a * CliffordAlgebra.ι source9Quadratic (source9CoordinateVector j) -
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector j) * a) i) hvalue).trans
      (congrFun (source9IdentityChartInverse_fderiv_zero_projected_commutator v (source9CoordinateVector j)) i)
  have hm : (fderiv ℝ (fun t : Fin 36 → ℝ =>
      ((source9SpinVectorOrthogonalHom (source9OrderedStrictPlaneWord t)) : Matrix SpaceIndex SpaceIndex ℝ)) 0) v =
        (A : Matrix SpaceIndex SpaceIndex ℝ) :=
    (source9OrderedStrictPlaneWord_matrix_fderiv_zero_model v).trans
      (congrArg (fun B : LieAlgebra.Orthogonal.so SpaceIndex ℝ => B.val)
        (source9OrderedStrictPlaneModelEquiv.apply_symm_apply A))
  have hd := source9OrderedStrictPlaneWord_matrix_hasFDerivAt_zero.fderiv
  have hv : source9PlaneWordMatrixVelocity source9StrictPlaneRow source9StrictPlaneColumn (List.finRange 36) v =
      (A : Matrix SpaceIndex SpaceIndex ℝ) :=
    (congrArg (fun L : (Fin 36 → ℝ) →L[ℝ] Matrix SpaceIndex SpaceIndex ℝ => L v) hd).symm.trans hm
  have hentry : source9PlaneWordVectorVelocity source9StrictPlaneRow source9StrictPlaneColumn
      (source9CoordinateVector j) (List.finRange 36) v i = A.val i j :=
    congrArg (fun M : Matrix SpaceIndex SpaceIndex ℝ => M i j) hv
  exact hcomm.trans hentry

#print axioms source9IdentityChartDerivative
#print axioms source9IdentityChartDerivativeRange
#print axioms source9NativeHalfBivectorSpan
#print axioms source9IdentityChartDerivative_apply
#print axioms source9IdentityChartDerivative_coordinate
#print axioms source9IdentityChartDerivative_range_eq_halfBivectorSpan
#print axioms source9IdentityChartDerivativeRangeEquiv
#print axioms source9IdentityChartDerivativeRangeEquiv_apply
#print axioms source9NativeSkewDerivativeRangeEquiv
#print axioms source9NativeSkewDerivativeRangeEquiv_apply
#print axioms source9NativeSkewDerivativeRangeEquiv_symm
#print axioms source9NativeSkewDerivativeRangeEquiv_projected_commutator
end
end FCP.BFSSPairedSpin9Clifford
