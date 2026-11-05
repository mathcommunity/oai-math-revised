import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8TSourcePositiveIYColorRealRotationProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8MOriginalJointGaussKernelGeneratedColorGaugeSubgroupProbe

/-!
L6H5E8U: FINITE original source Z(a) Y(b) Z(c) matrix product.

Qualified prerequisites:
- H5E8R #345: literal original +i Pauli-z scalar-exponential diagonal.
- H5E8S #348: literal original +i Pauli-y diagonal conjugation.
- H5E8T #349: literal original +i Pauli-y real rotation.
- H5E8M #330: exact original generated color subgroup.

The goal is an exact four-entry 2x2 product, with no introduction
of a substitute Lie group, source-sign reversal, or Fock-space
simplification. This is still *not* an Euler existence or full SU2
generation theorem. Those require separate explicit angle witnesses.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8U
noncomputable section

open Matrix
open OAI.BFSSQuantum
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6H5E8R
open FCP.BFSSSU2PhysicalDomainL6H5E8T
open FCP.BFSSSU2PhysicalDomainL6H5E8M

/-- Explicit product of the actual source z/y/z curves in the
original 2x2 color matrix representation. Each scalar exponent
uses the same positive-i normalized Pauli generator as H5E8R. -/
def sourceZYZMatrix (a b c : ℝ) : ColorMatrix 2 :=
  !![
    Complex.exp (sourceZDiagonal a 0) *
      (Real.cos (sourceYAngle b) : ℂ) *
      Complex.exp (sourceZDiagonal c 0),
    Complex.exp (sourceZDiagonal a 0) *
      (Real.sin (sourceYAngle b) : ℂ) *
      Complex.exp (sourceZDiagonal c 1);
    -(Complex.exp (sourceZDiagonal a 1) *
      (Real.sin (sourceYAngle b) : ℂ) *
      Complex.exp (sourceZDiagonal c 0)),
    Complex.exp (sourceZDiagonal a 1) *
      (Real.cos (sourceYAngle b) : ℂ) *
      Complex.exp (sourceZDiagonal c 1)
  ]

/-- Direct four-entry original-source Euler product identity.
No real-angle/complex-phase existence statement is assumed. -/
theorem original_source_zyz_matrix (a b c : ℝ) :
    (sourcePlusIGaugeCurve (2 : Fin 3) a : ColorMatrix 2) *
      (sourcePlusIGaugeCurve (1 : Fin 3) b : ColorMatrix 2) *
      (sourcePlusIGaugeCurve (2 : Fin 3) c : ColorMatrix 2) =
        sourceZYZMatrix a b c := by
  rw [source_z_gaugeCurve_diagonal_exp a,
      source_y_gaugeCurve_real_rotation b,
      source_z_gaugeCurve_diagonal_exp c]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceZYZMatrix, sourceYRotation, Matrix.mul_apply,
      Matrix.diagonal_apply]

/-- Transport the 2x2 matrix equality to multiplication of the
ACTUAL source GaugeGroup 2 elements. -/
theorem original_source_zyz_gauge_product_matrix (a b c : ℝ) :
    ((sourcePlusIGaugeCurve (2 : Fin 3) a *
        sourcePlusIGaugeCurve (1 : Fin 3) b *
        sourcePlusIGaugeCurve (2 : Fin 3) c : GaugeGroup 2) : ColorMatrix 2) =
      sourceZYZMatrix a b c := by
  change
    (sourcePlusIGaugeCurve (2 : Fin 3) a : ColorMatrix 2) *
      (sourcePlusIGaugeCurve (1 : Fin 3) b : ColorMatrix 2) *
      (sourcePlusIGaugeCurve (2 : Fin 3) c : ColorMatrix 2) =
        sourceZYZMatrix a b c
  exact original_source_zyz_matrix a b c

/-- Every concrete ZYZ product is in the subgroup generated
by the ORIGINAL source positive-i color curves. This is not
yet the assertion that every SU2 element has this product form. -/
theorem original_source_zyz_mem_generated (a b c : ℝ) :
    sourcePlusIGaugeCurve (2 : Fin 3) a *
      sourcePlusIGaugeCurve (1 : Fin 3) b *
      sourcePlusIGaugeCurve (2 : Fin 3) c ∈
        actualOriginalColorGeneratedSubgroup := by
  exact actualOriginalColorGeneratedSubgroup.mul_mem
    (actualOriginalColorGeneratedSubgroup.mul_mem
      (actualOriginalColorGaugeCurve_mem_generated (2 : Fin 3) a)
      (actualOriginalColorGaugeCurve_mem_generated (1 : Fin 3) b))
    (actualOriginalColorGaugeCurve_mem_generated (2 : Fin 3) c)

#print axioms sourceZYZMatrix
#print axioms original_source_zyz_matrix
#print axioms original_source_zyz_gauge_product_matrix
#print axioms original_source_zyz_mem_generated
#check @original_source_zyz_gauge_product_matrix

end
end FCP.BFSSSU2PhysicalDomainL6H5E8U
