import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CYIdentityChartDerivativeRange
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BKCoordinatePlaneVelocityComparison

/-! F10CZ: original-gamma evaluation on the exact chart derivative range matches F10BB.
Extend the accepted positive half-bivector coordinate comparison by real linearity. Then
compute the ordinary finite-parameter derivative of the existing F10BC SO(16) homomorphism
composed with the literal chart inverse. No source tangent-space identification, range bracket
compatibility, manifold differential, integration/lift or BFSS physical conclusion is asserted.
Candidate until strict source compilation and complete independent audit. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9Plane
open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

local instance f10czLocalNormedAddCommGroup :
    NormedAddCommGroup (CliffordAlgebra source9Quadratic) := source9PBWNormedAddCommGroup
local instance f10czLocalNormedSpace :
    NormedSpace ℝ (CliffordAlgebra source9Quadratic) := source9PBWNormedSpace

/-- Original Clifford gamma evaluation agrees in every parameter direction, with unchanged factors. -/
theorem source9IdentityChartDerivative_originalGamma (v : Fin 36 → ℝ) :
    source9GammaCliffordAlgHom (source9IdentityChartDerivative v) =
      coordinateToOriginalGammaLinearMap
        (source9OrderedStrictPlaneModelEquiv v : Matrix SpaceIndex SpaceIndex ℝ) := by
  have hL : source9IdentityChartDerivative v =
      ∑ i : Fin 36, v i • ((1 / 2 : ℝ) •
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneRow i)) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneColumn i)))) := by
    have h := source9IdentityChartDerivative_apply v
    rw [← Fin.sum_univ_def] at h
    exact h
  have hM : (source9OrderedStrictPlaneModelEquiv v : Matrix SpaceIndex SpaceIndex ℝ) =
      ∑ i : Fin 36, v i • coordinatePlane9 (source9StrictPlaneRow i) (source9StrictPlaneColumn i) := by
    have h := (source9OrderedStrictPlane_sum_eq_model v).symm
    rw [← Fin.sum_univ_def] at h
    exact h
  rw [hL, hM, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hplane : source9GammaCliffordAlgHom
      ((1 / 2 : ℝ) •
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneRow i)) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneColumn i)))) =
      coordinateToOriginalGammaLinearMap
        (coordinatePlane9 (source9StrictPlaneRow i) (source9StrictPlaneColumn i)) :=
    source9PlaneCliffordVelocity_gamma_eq_coordinatePlaneLieHom
      (source9StrictPlaneRow i) (source9StrictPlaneColumn i) (source9StrictPlaneEnumeration_ne i)
  calc
    source9GammaCliffordAlgHom (v i • ((1 / 2 : ℝ) •
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneRow i)) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneColumn i))))) =
        v i • source9GammaCliffordAlgHom ((1 / 2 : ℝ) •
          (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneRow i)) *
            CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneColumn i)))) :=
      map_smul source9GammaCliffordAlgHom (v i) _
    _ = v i • coordinateToOriginalGammaLinearMap
        (coordinatePlane9 (source9StrictPlaneRow i) (source9StrictPlaneColumn i)) :=
      congrArg (fun M : GammaMatrix => v i • M) hplane
    _ = coordinateToOriginalGammaLinearMap
        (v i • coordinatePlane9 (source9StrictPlaneRow i) (source9StrictPlaneColumn i)) :=
      (map_smul coordinateToOriginalGammaLinearMap (v i) _).symm

/-- The CY range coordinate corresponding to any canonical native skew input evaluates to F10BB. -/
theorem source9NativeSkewDerivativeRangeEquiv_originalGamma
    (A : LieAlgebra.Orthogonal.so SpaceIndex ℝ) :
    source9GammaCliffordAlgHom
      (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) =
        (coordinateToOriginalGammaSkewLieHom A : GammaMatrix) := by
  have hvalue := source9NativeSkewDerivativeRangeEquiv_apply A
  have hpoint := source9IdentityChartDerivative_originalGamma (source9OrderedStrictPlaneModelEquiv.symm A)
  have hmatrix : (source9OrderedStrictPlaneModelEquiv (source9OrderedStrictPlaneModelEquiv.symm A) :
      Matrix SpaceIndex SpaceIndex ℝ) = (A : Matrix SpaceIndex SpaceIndex ℝ) :=
    congrArg (fun B : LieAlgebra.Orthogonal.so SpaceIndex ℝ => B.val)
      (source9OrderedStrictPlaneModelEquiv.apply_symm_apply A)
  have htarget : coordinateToOriginalGammaLinearMap
      (source9OrderedStrictPlaneModelEquiv (source9OrderedStrictPlaneModelEquiv.symm A) :
        Matrix SpaceIndex SpaceIndex ℝ) = (coordinateToOriginalGammaSkewLieHom A : GammaMatrix) :=
    congrArg coordinateToOriginalGammaLinearMap hmatrix
  exact (congrArg source9GammaCliffordAlgHom hvalue).trans (hpoint.trans htarget)

/-- Every actual range value has the original-gamma image specified by its inverse native coordinate. -/
theorem source9DerivativeRange_originalGamma (x : source9IdentityChartDerivativeRange) :
    source9GammaCliffordAlgHom (x : CliffordAlgebra source9Quadratic) =
      (coordinateToOriginalGammaSkewLieHom (source9NativeSkewDerivativeRangeEquiv.symm x) : GammaMatrix) := by
  have heq : (source9NativeSkewDerivativeRangeEquiv (source9NativeSkewDerivativeRangeEquiv.symm x) :
      CliffordAlgebra source9Quadratic) = (x : CliffordAlgebra source9Quadratic) :=
    congrArg (fun y : source9IdentityChartDerivativeRange => (y : CliffordAlgebra source9Quadratic))
      (source9NativeSkewDerivativeRangeEquiv.apply_symm_apply x)
  exact (congrArg source9GammaCliffordAlgHom heq).symm.trans
    (source9NativeSkewDerivativeRangeEquiv_originalGamma (source9NativeSkewDerivativeRangeEquiv.symm x))

theorem source9NativeSkewDerivativeRangeEquiv_gamma_mem_so
    (A : LieAlgebra.Orthogonal.so SpaceIndex ℝ) :
    source9GammaCliffordAlgHom
      (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) ∈
        LieAlgebra.Orthogonal.so SpinIndex ℝ :=
  (source9NativeSkewDerivativeRangeEquiv_originalGamma A).symm ▸
    (coordinateToOriginalGammaSkewLieHom A).property

/-- The already accepted whole-Clifford original-gamma linear evaluation with its existing continuity. -/
noncomputable def source9OriginalGammaEvaluationCLM :
    CliffordAlgebra source9Quadratic →L[ℝ] GammaMatrix :=
  { toLinearMap := source9GammaCliffordAlgHom.toLinearMap
    cont := source9GammaCliffordAlgHom_continuous_pbw }

theorem source9OriginalGammaEvaluationCLM_apply (x : CliffordAlgebra source9Quadratic) :
    source9OriginalGammaEvaluationCLM x = source9GammaCliffordAlgHom x := rfl

/-- Ordinary parameter-space derivative of the actual F10BC image along the exact chart inverse. -/
theorem source9IdentityChartInverse_originalGamma_hasFDerivAt_zero :
    HasFDerivAt (fun t : Fin 36 → ℝ =>
      ((source9SpinGammaSpecialOrthogonalHom (source9SpinIdentityLocalChart.symm t)) : GammaMatrix))
      (source9OriginalGammaEvaluationCLM.comp source9IdentityChartDerivative) 0 := by
  have hL : source9IdentityChartDerivative =
      source9PlaneSpinWordVelocity source9StrictPlaneRow source9StrictPlaneColumn (List.finRange 36) :=
    source9IdentityChartInverse_clifford_fderiv_zero
  have hC : HasFDerivAt (fun t : Fin 36 → ℝ =>
      ((source9SpinIdentityLocalChart.symm t) : CliffordAlgebra source9Quadratic))
      source9IdentityChartDerivative 0 :=
    Eq.mp (congrArg (fun D : (Fin 36 → ℝ) →L[ℝ] CliffordAlgebra source9Quadratic =>
      HasFDerivAt (fun t : Fin 36 → ℝ =>
        ((source9SpinIdentityLocalChart.symm t) : CliffordAlgebra source9Quadratic)) D 0) hL.symm)
      source9IdentityChartInverse_clifford_hasFDerivAt_zero
  have h : HasFDerivAt (fun t : Fin 36 → ℝ =>
      source9OriginalGammaEvaluationCLM
        ((source9SpinIdentityLocalChart.symm t) : CliffordAlgebra source9Quadratic))
      (source9OriginalGammaEvaluationCLM.comp source9IdentityChartDerivative) 0 :=
    source9OriginalGammaEvaluationCLM.hasFDerivAt.comp (0 : Fin 36 → ℝ) hC
  have heq : (fun t : Fin 36 → ℝ =>
      source9OriginalGammaEvaluationCLM
        ((source9SpinIdentityLocalChart.symm t) : CliffordAlgebra source9Quadratic)) =
      (fun t : Fin 36 → ℝ =>
        ((source9SpinGammaSpecialOrthogonalHom (source9SpinIdentityLocalChart.symm t)) : GammaMatrix)) := by
    funext t
    exact (source9SpinGammaSpecialOrthogonalHom_apply (source9SpinIdentityLocalChart.symm t)).symm
  rw [heq] at h
  exact h

theorem source9IdentityChartInverse_originalGamma_fderiv_zero_apply (v : Fin 36 → ℝ) :
    (fderiv ℝ (fun t : Fin 36 → ℝ =>
      ((source9SpinGammaSpecialOrthogonalHom (source9SpinIdentityLocalChart.symm t)) : GammaMatrix)) 0) v =
      (coordinateToOriginalGammaSkewLieHom (source9OrderedStrictPlaneModelEquiv v) : GammaMatrix) := by
  have hvalue : (fderiv ℝ (fun t : Fin 36 → ℝ =>
      ((source9SpinGammaSpecialOrthogonalHom (source9SpinIdentityLocalChart.symm t)) : GammaMatrix)) 0) v =
      source9GammaCliffordAlgHom (source9IdentityChartDerivative v) :=
    congrArg (fun L : (Fin 36 → ℝ) →L[ℝ] GammaMatrix => L v)
      source9IdentityChartInverse_originalGamma_hasFDerivAt_zero.fderiv
  exact hvalue.trans (source9IdentityChartDerivative_originalGamma v)

/-- Full linear-operator factorization in the original gamma carrier, without a manifold claim. -/
theorem source9IdentityChartInverse_originalGamma_fderiv_zero_factor :
    (fderiv ℝ (fun t : Fin 36 → ℝ =>
      ((source9SpinGammaSpecialOrthogonalHom (source9SpinIdentityLocalChart.symm t)) : GammaMatrix)) 0).toLinearMap =
      (((LieAlgebra.Orthogonal.so SpinIndex ℝ).toSubmodule.subtype.comp
        coordinateToOriginalGammaSkewLieHom.toLinearMap).comp source9OrderedStrictPlaneModelEquiv.toLinearMap) := by
  apply LinearMap.ext
  intro v
  exact source9IdentityChartInverse_originalGamma_fderiv_zero_apply v

#print axioms source9IdentityChartDerivative_originalGamma
#print axioms source9NativeSkewDerivativeRangeEquiv_originalGamma
#print axioms source9DerivativeRange_originalGamma
#print axioms source9NativeSkewDerivativeRangeEquiv_gamma_mem_so
#print axioms source9OriginalGammaEvaluationCLM
#print axioms source9OriginalGammaEvaluationCLM_apply
#print axioms source9IdentityChartInverse_originalGamma_hasFDerivAt_zero
#print axioms source9IdentityChartInverse_originalGamma_fderiv_zero_apply
#print axioms source9IdentityChartInverse_originalGamma_fderiv_zero_factor
end
end FCP.BFSSPairedSpin9Clifford
