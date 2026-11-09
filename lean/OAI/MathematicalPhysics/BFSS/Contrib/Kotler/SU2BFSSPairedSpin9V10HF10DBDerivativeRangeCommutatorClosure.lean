import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10DADerivativeRangeCommutatorAction
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CTExteriorScalarKernel
import Mathlib.LinearAlgebra.CliffordAlgebra.Even

/-! F10DB: eliminate the exact native-range bracket defect using proved evenness.
The original even commutator/contraction identity and exterior scalar-kernel theorem apply
to arbitrary even Clifford elements. Scalar gamma evaluation is faithful; whole-Clifford
gamma faithfulness is not assumed. Prove actual range closure and native bracket equality.
No range Lie algebra/equivalence, source tangent identification or manifold differential is
packaged. Candidate until complete fresh strict compilation and independent audit. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open FCP.BFSSGamma9
open scoped Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

local instance f10dbLocalNormedAddCommGroup :
    NormedAddCommGroup (CliffordAlgebra source9Quadratic) := source9PBWNormedAddCommGroup
local instance f10dbLocalNormedSpace :
    NormedSpace ℝ (CliffordAlgebra source9Quadratic) := source9PBWNormedSpace

/-- Evenness and literal vector commutation imply zero contraction against every original dual. -/
theorem source9Clifford_even_commutes_coordinateContractions_zero
    (x : CliffordAlgebra source9Quadratic) (hx : x ∈ CliffordAlgebra.even source9Quadratic)
    (hc : ∀ z : SpaceIndex → ℝ,
      x * CliffordAlgebra.ι source9Quadratic z = CliffordAlgebra.ι source9Quadratic z * x) :
    ∀ j : SpaceIndex, CliffordAlgebra.contractLeft (Q := source9Quadratic)
      (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ)) x = 0 := by
  intro j
  rw [← source9Polar_halfCoordinate_eq_coordinateDual j]
  have h := source9Clifford_evenCommutator_eq_polarContraction
    ((1 / 2 : ℝ) • source9CoordinateVector j) x hx
  rw [(hc ((1 / 2 : ℝ) • source9CoordinateVector j)).symm, sub_self] at h
  exact h.symm

/-- Scalar classification for arbitrary even commutants, with no Spin-group membership premise. -/
theorem source9Clifford_even_commutes_eq_scalar
    (x : CliffordAlgebra source9Quadratic) (hx : x ∈ CliffordAlgebra.even source9Quadratic)
    (hc : ∀ z : SpaceIndex → ℝ,
      x * CliffordAlgebra.ι source9Quadratic z = CliffordAlgebra.ι source9Quadratic z * x) :
    ∃ c : ℝ, x = algebraMap ℝ (CliffordAlgebra source9Quadratic) c := by
  have hzero := source9Clifford_even_commutes_coordinateContractions_zero x hx hc
  have hext : ∀ j : SpaceIndex,
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (SpaceIndex → ℝ)))
        (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ))
        ((CliffordAlgebra.equivExterior source9Quadratic) x) = 0 := by
    intro j
    exact (source9Clifford_contractLeft_zero_iff_exterior
      (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ)) x).1 (hzero j)
  obtain ⟨c, hcscalar⟩ := (source9Exterior_commonCoordinateKernel_iff_scalar
    ((CliffordAlgebra.equivExterior source9Quadratic) x)).1 hext
  exact ⟨c, (source9Clifford_exterior_eq_scalar_iff x c).1 hcscalar⟩

/-- Zero gamma image eliminates an even commutant using only real scalar faithfulness. -/
theorem source9Clifford_even_commutes_gamma_zero
    (x : CliffordAlgebra source9Quadratic) (hx : x ∈ CliffordAlgebra.even source9Quadratic)
    (hc : ∀ z : SpaceIndex → ℝ,
      x * CliffordAlgebra.ι source9Quadratic z = CliffordAlgebra.ι source9Quadratic z * x)
    (hgamma : source9GammaCliffordAlgHom x = 0) : x = 0 := by
  obtain ⟨c, hscalar⟩ := source9Clifford_even_commutes_eq_scalar x hx hc
  have himage : source9GammaCliffordAlgHom
      (algebraMap ℝ (CliffordAlgebra source9Quadratic) c) = 0 :=
    (congrArg source9GammaCliffordAlgHom hscalar).symm.trans hgamma
  have htarget : algebraMap ℝ GammaMatrix c = 0 :=
    (source9GammaCliffordAlgHom.commutes c).symm.trans himage
  have hc0 : c = 0 := (FaithfulSMul.algebraMap_injective ℝ GammaMatrix)
    (htarget.trans (map_zero (algebraMap ℝ GammaMatrix)).symm)
  exact hscalar.trans ((congrArg (algebraMap ℝ (CliffordAlgebra source9Quadratic)) hc0).trans
    (map_zero (algebraMap ℝ (CliffordAlgebra source9Quadratic))))

/-- Every actual derivative-range value is in the original even Clifford subalgebra. -/
theorem source9IdentityChartDerivativeRange_mem_even (x : source9IdentityChartDerivativeRange) :
    (x : CliffordAlgebra source9Quadratic) ∈ CliffordAlgebra.even source9Quadratic := by
  have hspan : source9NativeHalfBivectorSpan ≤
      (CliffordAlgebra.even source9Quadratic).toSubmodule := by
    change Submodule.span ℝ (Set.range (fun p : source9StrictPlaneIndex =>
      (1 / 2 : ℝ) •
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector p.val.1) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector p.val.2)))) ≤ _
    apply Submodule.span_le.2
    rintro y ⟨p, rfl⟩
    exact (CliffordAlgebra.even source9Quadratic).toSubmodule.smul_mem (1 / 2 : ℝ)
      (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero source9Quadratic
        (source9CoordinateVector p.val.1) (source9CoordinateVector p.val.2))
  have hx : (x : CliffordAlgebra source9Quadratic) ∈ source9NativeHalfBivectorSpan :=
    source9IdentityChartDerivative_range_eq_halfBivectorSpan ▸ x.property
  exact hspan hx

/-- Prove evenness of the literal defect before applying any commutant scalar theorem. -/
theorem source9NativeSkewDerivativeRange_bracket_defect_mem_even
    (A B : LieAlgebra.Orthogonal.so SpaceIndex ℝ) :
    ((source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) *
        (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) -
      (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) *
        (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) -
      (source9NativeSkewDerivativeRangeEquiv ⁅A, B⁆ : CliffordAlgebra source9Quadratic)) ∈
        CliffordAlgebra.even source9Quadratic := by
  have hA := source9IdentityChartDerivativeRange_mem_even (source9NativeSkewDerivativeRangeEquiv A)
  have hB := source9IdentityChartDerivativeRange_mem_even (source9NativeSkewDerivativeRangeEquiv B)
  have hbr := source9IdentityChartDerivativeRange_mem_even (source9NativeSkewDerivativeRangeEquiv ⁅A, B⁆)
  exact (CliffordAlgebra.even source9Quadratic).sub_mem
    ((CliffordAlgebra.even source9Quadratic).sub_mem
      ((CliffordAlgebra.even source9Quadratic).mul_mem hA hB)
      ((CliffordAlgebra.even source9Quadratic).mul_mem hB hA)) hbr

/-- The exact accepted DA defect vanishes, with all parity, commutation and gamma premises proved. -/
theorem source9NativeSkewDerivativeRange_bracket_defect_zero
    (A B : LieAlgebra.Orthogonal.so SpaceIndex ℝ) :
    (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) *
        (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) -
      (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) *
        (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) -
      (source9NativeSkewDerivativeRangeEquiv ⁅A, B⁆ : CliffordAlgebra source9Quadratic) = 0 :=
  source9Clifford_even_commutes_gamma_zero _
    (source9NativeSkewDerivativeRange_bracket_defect_mem_even A B)
    (source9NativeSkewDerivativeRange_bracket_defect_commutes A B)
    (source9NativeSkewDerivativeRange_bracket_defect_gamma_zero A B)

/-- The existing native real-linear range equivalence preserves the literal ambient commutator. -/
theorem source9NativeSkewDerivativeRangeEquiv_commutator
    (A B : LieAlgebra.Orthogonal.so SpaceIndex ℝ) :
    (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) *
        (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) -
      (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) *
        (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) =
      (source9NativeSkewDerivativeRangeEquiv ⁅A, B⁆ : CliffordAlgebra source9Quadratic) :=
  sub_eq_zero.mp (source9NativeSkewDerivativeRange_bracket_defect_zero A B)

/-- Closure holds for arbitrary values of the actual original Clifford derivative range. -/
theorem source9IdentityChartDerivativeRange_commutator_mem
    (x y : source9IdentityChartDerivativeRange) :
    ((x : CliffordAlgebra source9Quadratic) * (y : CliffordAlgebra source9Quadratic) -
      (y : CliffordAlgebra source9Quadratic) * (x : CliffordAlgebra source9Quadratic)) ∈
        source9IdentityChartDerivativeRange := by
  let A := source9NativeSkewDerivativeRangeEquiv.symm x
  let B := source9NativeSkewDerivativeRangeEquiv.symm y
  have hx : (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) =
      (x : CliffordAlgebra source9Quadratic) :=
    congrArg (fun z : source9IdentityChartDerivativeRange => (z : CliffordAlgebra source9Quadratic))
      (source9NativeSkewDerivativeRangeEquiv.apply_symm_apply x)
  have hy : (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) =
      (y : CliffordAlgebra source9Quadratic) :=
    congrArg (fun z : source9IdentityChartDerivativeRange => (z : CliffordAlgebra source9Quadratic))
      (source9NativeSkewDerivativeRangeEquiv.apply_symm_apply y)
  have hmem :
      ((source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) *
          (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) -
        (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) *
          (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic)) ∈
            source9IdentityChartDerivativeRange :=
    (source9NativeSkewDerivativeRange_commutator_mem_iff_bracket A B).2
      (source9NativeSkewDerivativeRangeEquiv_commutator A B)
  rw [hx, hy] at hmem
  exact hmem

/-- The identical native increasing-half-bivector span is also closed under this ambient commutator. -/
theorem source9NativeHalfBivectorSpan_commutator_mem
    (x y : CliffordAlgebra source9Quadratic)
    (hx : x ∈ source9NativeHalfBivectorSpan) (hy : y ∈ source9NativeHalfBivectorSpan) :
    x * y - y * x ∈ source9NativeHalfBivectorSpan := by
  have hxR : x ∈ source9IdentityChartDerivativeRange :=
    source9IdentityChartDerivative_range_eq_halfBivectorSpan.symm ▸ hx
  have hyR : y ∈ source9IdentityChartDerivativeRange :=
    source9IdentityChartDerivative_range_eq_halfBivectorSpan.symm ▸ hy
  have hmem : x * y - y * x ∈ source9IdentityChartDerivativeRange :=
    source9IdentityChartDerivativeRange_commutator_mem ⟨x, hxR⟩ ⟨y, hyR⟩
  exact source9IdentityChartDerivative_range_eq_halfBivectorSpan ▸ hmem

#print axioms source9Clifford_even_commutes_coordinateContractions_zero
#print axioms source9Clifford_even_commutes_eq_scalar
#print axioms source9Clifford_even_commutes_gamma_zero
#print axioms source9IdentityChartDerivativeRange_mem_even
#print axioms source9NativeSkewDerivativeRange_bracket_defect_mem_even
#print axioms source9NativeSkewDerivativeRange_bracket_defect_zero
#print axioms source9NativeSkewDerivativeRangeEquiv_commutator
#print axioms source9IdentityChartDerivativeRange_commutator_mem
#print axioms source9NativeHalfBivectorSpan_commutator_mem
end
end FCP.BFSSPairedSpin9Clifford
