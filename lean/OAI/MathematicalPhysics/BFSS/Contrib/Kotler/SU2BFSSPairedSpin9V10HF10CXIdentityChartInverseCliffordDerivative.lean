import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CWOriginalSourceIdentityLocalChart

/-! F10CX: original Clifford-valued regularity and derivative of the exact identity-chart inverse.
Transport the accepted finite-word results through CW's literal actual-word inverse formula.
The ambient derivative is the ordered positive half-bivector sum and is injective, as witnessed
by its projected commutator and the accepted injective native natural-matrix derivative.
No source tangent-space identification, manifold instance, full group-map differential or
physical BFSS conclusion is asserted. Candidate until strict compilation and independent audit. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open scoped ContDiff Matrix.Norms.Elementwise

local instance f10cxLocalNormedAddCommGroup :
    NormedAddCommGroup (CliffordAlgebra source9Quadratic) := source9PBWNormedAddCommGroup
local instance f10cxLocalNormedSpace :
    NormedSpace ℝ (CliffordAlgebra source9Quadratic) := source9PBWNormedSpace

/-- Exact total inverse in the original Clifford carrier; the chart laws remain domain restricted. -/
theorem source9IdentityChartInverse_clifford_eq_word :
    (fun t : Fin 36 → ℝ =>
      ((source9SpinIdentityLocalChart.symm t) : CliffordAlgebra source9Quadratic)) =
    (fun t : Fin 36 → ℝ =>
      ((source9OrderedStrictPlaneWord t) : CliffordAlgebra source9Quadratic)) := by
  funext t
  exact congrArg (fun g : spinGroup source9Quadratic => (g : CliffordAlgebra source9Quadratic))
    (congrFun source9SpinIdentityLocalChart_symm_coe t)

/-- Every-order regularity is ambient Clifford-valued regularity of this exact actual inverse. -/
theorem source9IdentityChartInverse_clifford_contDiff_pbw (n : ℕ∞ω) :
    ContDiff ℝ n (fun t : Fin 36 → ℝ =>
      ((source9SpinIdentityLocalChart.symm t) : CliffordAlgebra source9Quadratic)) := by
  rw [source9IdentityChartInverse_clifford_eq_word]
  exact source9PlaneSpinWord_coe_contDiff_pbw n source9StrictPlaneRow source9StrictPlaneColumn
    source9StrictPlaneEnumeration_ne (List.finRange 36)

theorem source9IdentityChartInverse_clifford_hasFDerivAt_zero :
    HasFDerivAt (fun t : Fin 36 → ℝ =>
      ((source9SpinIdentityLocalChart.symm t) : CliffordAlgebra source9Quadratic))
      (source9PlaneSpinWordVelocity source9StrictPlaneRow source9StrictPlaneColumn (List.finRange 36)) 0 := by
  rw [source9IdentityChartInverse_clifford_eq_word]
  exact source9PlaneSpinWord_coe_hasFDerivAt_zero source9StrictPlaneRow source9StrictPlaneColumn
    source9StrictPlaneEnumeration_ne (List.finRange 36)

theorem source9IdentityChartInverse_clifford_fderiv_zero :
    fderiv ℝ (fun t : Fin 36 → ℝ =>
      ((source9SpinIdentityLocalChart.symm t) : CliffordAlgebra source9Quadratic)) 0 =
      source9PlaneSpinWordVelocity source9StrictPlaneRow source9StrictPlaneColumn (List.finRange 36) :=
  source9IdentityChartInverse_clifford_hasFDerivAt_zero.fderiv

/-- Preserve the original half factor, orientation and chosen parameter-index order. -/
theorem source9IdentityChartInverse_clifford_fderiv_zero_apply (v : Fin 36 → ℝ) :
    (fderiv ℝ (fun t : Fin 36 → ℝ =>
      ((source9SpinIdentityLocalChart.symm t) : CliffordAlgebra source9Quadratic)) 0) v =
      ((List.finRange 36).map (fun i => v i • ((1 / 2 : ℝ) •
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneRow i)) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (source9StrictPlaneColumn i)))))).sum := by
  exact (congrArg (fun L : (Fin 36 → ℝ) →L[ℝ] CliffordAlgebra source9Quadratic => L v)
    source9IdentityChartInverse_clifford_fderiv_zero).trans
      (source9PlaneSpinWordVelocity_apply source9StrictPlaneRow source9StrictPlaneColumn (List.finRange 36) v)

theorem source9IdentityChartInverse_clifford_fderiv_zero_reverse (v : Fin 36 → ℝ) :
    CliffordAlgebra.reverse ((fderiv ℝ (fun t : Fin 36 → ℝ =>
      ((source9SpinIdentityLocalChart.symm t) : CliffordAlgebra source9Quadratic)) 0) v) =
      -((fderiv ℝ (fun t : Fin 36 → ℝ =>
        ((source9SpinIdentityLocalChart.symm t) : CliffordAlgebra source9Quadratic)) 0) v) := by
  rw [source9IdentityChartInverse_clifford_fderiv_zero]
  exact source9PlaneSpinWordVelocity_reverse source9StrictPlaneRow source9StrictPlaneColumn
    source9StrictPlaneEnumeration_ne (List.finRange 36) v

/-- The actual ambient chart-inverse derivative has the accepted full native-vector commutator. -/
theorem source9IdentityChartInverse_fderiv_zero_projected_commutator
    (v : Fin 36 → ℝ) (z : SpaceIndex → ℝ) :
    source9CliffordVectorProjection
      (((fderiv ℝ (fun t : Fin 36 → ℝ =>
        ((source9SpinIdentityLocalChart.symm t) : CliffordAlgebra source9Quadratic)) 0) v) *
          CliffordAlgebra.ι source9Quadratic z -
        CliffordAlgebra.ι source9Quadratic z *
          ((fderiv ℝ (fun t : Fin 36 → ℝ =>
            ((source9SpinIdentityLocalChart.symm t) : CliffordAlgebra source9Quadratic)) 0) v)) =
      source9PlaneWordVectorVelocity source9StrictPlaneRow source9StrictPlaneColumn z (List.finRange 36) v := by
  have hvalue :
      (fderiv ℝ (fun t : Fin 36 → ℝ =>
        ((source9SpinIdentityLocalChart.symm t) : CliffordAlgebra source9Quadratic)) 0) v =
        source9PlaneSpinWordVelocity source9StrictPlaneRow source9StrictPlaneColumn (List.finRange 36) v :=
    congrArg (fun L : (Fin 36 → ℝ) →L[ℝ] CliffordAlgebra source9Quadratic => L v)
      source9IdentityChartInverse_clifford_fderiv_zero
  exact (congrArg (fun a : CliffordAlgebra source9Quadratic =>
    source9CliffordVectorProjection
      (a * CliffordAlgebra.ι source9Quadratic z - CliffordAlgebra.ι source9Quadratic z * a))
    hvalue).trans (source9PlaneSpinWordVelocity_projected_commutator source9StrictPlaneRow source9StrictPlaneColumn
      (List.finRange 36) v z)

/-- Actual natural-matrix action of the chart inverse retains the existing canonical native model. -/
theorem source9IdentityChartInverse_naturalMatrix_fderiv_zero_model (v : Fin 36 → ℝ) :
    (fderiv ℝ (fun t : Fin 36 → ℝ =>
      ((source9SpinVectorOrthogonalHom (source9SpinIdentityLocalChart.symm t)) :
        Matrix SpaceIndex SpaceIndex ℝ)) 0) v =
      (source9OrderedStrictPlaneModelEquiv v : Matrix SpaceIndex SpaceIndex ℝ) := by
  have heq : (fun t : Fin 36 → ℝ =>
      ((source9SpinVectorOrthogonalHom (source9SpinIdentityLocalChart.symm t)) :
        Matrix SpaceIndex SpaceIndex ℝ)) =
      (fun t : Fin 36 → ℝ =>
        ((source9SpinVectorOrthogonalHom (source9OrderedStrictPlaneWord t)) :
          Matrix SpaceIndex SpaceIndex ℝ)) := by
    funext t
    exact congrArg (fun g : spinGroup source9Quadratic =>
      ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ))
        (congrFun source9SpinIdentityLocalChart_symm_coe t)
  rw [heq]
  exact source9OrderedStrictPlaneWord_matrix_fderiv_zero_model v

/-- Injectivity of this ambient derivative prepares, but does not identify, the source tangent space. -/
theorem source9IdentityChartInverse_clifford_fderiv_zero_injective :
    Function.Injective (fun v : Fin 36 → ℝ =>
      (fderiv ℝ (fun t : Fin 36 → ℝ =>
        ((source9SpinIdentityLocalChart.symm t) : CliffordAlgebra source9Quadratic)) 0) v) := by
  intro v w hvw
  apply source9OrderedStrictPlaneWord_matrix_fderiv_zero_injective
  have hmatrix :
      source9PlaneWordMatrixVelocity source9StrictPlaneRow source9StrictPlaneColumn (List.finRange 36) v =
      source9PlaneWordMatrixVelocity source9StrictPlaneRow source9StrictPlaneColumn (List.finRange 36) w := by
    apply Matrix.ext
    intro i j
    change source9PlaneWordVectorVelocity source9StrictPlaneRow source9StrictPlaneColumn
      (source9CoordinateVector j) (List.finRange 36) v i =
        source9PlaneWordVectorVelocity source9StrictPlaneRow source9StrictPlaneColumn
          (source9CoordinateVector j) (List.finRange 36) w i
    have hcomm := congrArg (fun a : CliffordAlgebra source9Quadratic =>
      source9CliffordVectorProjection
        (a * CliffordAlgebra.ι source9Quadratic (source9CoordinateVector j) -
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector j) * a) i) hvw
    exact (congrFun (source9IdentityChartInverse_fderiv_zero_projected_commutator v
      (source9CoordinateVector j)) i).symm.trans
        (hcomm.trans (congrFun (source9IdentityChartInverse_fderiv_zero_projected_commutator w
          (source9CoordinateVector j)) i))
  have hd := source9OrderedStrictPlaneWord_matrix_hasFDerivAt_zero.fderiv
  exact (congrArg (fun L : (Fin 36 → ℝ) →L[ℝ] Matrix SpaceIndex SpaceIndex ℝ => L v) hd).trans
    (hmatrix.trans (congrArg (fun L : (Fin 36 → ℝ) →L[ℝ] Matrix SpaceIndex SpaceIndex ℝ => L w) hd).symm)

#print axioms source9IdentityChartInverse_clifford_eq_word
#print axioms source9IdentityChartInverse_clifford_contDiff_pbw
#print axioms source9IdentityChartInverse_clifford_hasFDerivAt_zero
#print axioms source9IdentityChartInverse_clifford_fderiv_zero
#print axioms source9IdentityChartInverse_clifford_fderiv_zero_apply
#print axioms source9IdentityChartInverse_clifford_fderiv_zero_reverse
#print axioms source9IdentityChartInverse_fderiv_zero_projected_commutator
#print axioms source9IdentityChartInverse_naturalMatrix_fderiv_zero_model
#print axioms source9IdentityChartInverse_clifford_fderiv_zero_injective
end
end FCP.BFSSPairedSpin9Clifford
