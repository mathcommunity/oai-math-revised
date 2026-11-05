import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8WOriginalSU2SourceEulerTimePhaseProbe

/-!
L6H5E8X — genuine original SU2 first-row Euler reconstruction.

Qualified H5E8U #350: literal source positive-i ZYZ product matrix.
Qualified H5E8V #351: zero-safe genuine original SU2 polar radii.
Qualified H5E8W #354: exact original source Pauli Euler times and
both scalar exponential phase products.

Only first-row entries are proved here, with all source signs
and times intact. A full GaugeGroup 2 Euler existence statement,
generated subgroup = top, and physical-space equivalence remain
independent, unqualified targets.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8X
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6H5E8R
open FCP.BFSSSU2PhysicalDomainL6H5E8T
open FCP.BFSSSU2PhysicalDomainL6H5E8U
open FCP.BFSSSU2PhysicalDomainL6H5E8V
open FCP.BFSSSU2PhysicalDomainL6H5E8W

/-- Exact (0,0) coefficient of the genuine original-source
ZYZ matrix at the explicitly constructed source Euler times. -/
theorem original_source_zyz_firstRow_u (g : GaugeGroup 2) :
    (sourceZYZMatrix
      (originalEulerLeftTime g)
      (originalEulerMiddleTime g)
      (originalEulerRightTime g)) 0 0 = originalSU2RowU g := by
  calc
    _ = Complex.exp (sourceZDiagonal (originalEulerLeftTime g) 0) *
          (Real.cos (sourceYAngle (originalEulerMiddleTime g)) : ℂ) *
          Complex.exp (sourceZDiagonal (originalEulerRightTime g) 0) := by
            simp [sourceZYZMatrix]
    _ = (‖originalSU2RowU g‖ : ℂ) *
          (Complex.exp (sourceZDiagonal (originalEulerLeftTime g) 0) *
            Complex.exp (sourceZDiagonal (originalEulerRightTime g) 0)) := by
            rw [originalEuler_sourceY_middle, originalSU2_middle_cos]
            ring
    _ = (‖originalSU2RowU g‖ : ℂ) *
          Complex.exp (Complex.arg (originalSU2RowU g) * Complex.I) := by
            rw [originalEuler_source_exp_phase_u]
    _ = originalSU2RowU g := originalSU2_row_u_zero_safe_polar g

/-- Exact (0,1) coefficient of the genuine original-source
ZYZ matrix, including the v=0 case. -/
theorem original_source_zyz_firstRow_v (g : GaugeGroup 2) :
    (sourceZYZMatrix
      (originalEulerLeftTime g)
      (originalEulerMiddleTime g)
      (originalEulerRightTime g)) 0 1 = originalSU2RowV g := by
  calc
    _ = Complex.exp (sourceZDiagonal (originalEulerLeftTime g) 0) *
          (Real.sin (sourceYAngle (originalEulerMiddleTime g)) : ℂ) *
          Complex.exp (sourceZDiagonal (originalEulerRightTime g) 1) := by
            simp [sourceZYZMatrix]
    _ = (‖originalSU2RowV g‖ : ℂ) *
          (Complex.exp (sourceZDiagonal (originalEulerLeftTime g) 0) *
            Complex.exp (sourceZDiagonal (originalEulerRightTime g) 1)) := by
            rw [originalEuler_sourceY_middle, originalSU2_middle_sin]
            ring
    _ = (‖originalSU2RowV g‖ : ℂ) *
          Complex.exp (Complex.arg (originalSU2RowV g) * Complex.I) := by
            rw [originalEuler_source_exp_phase_v]
    _ = originalSU2RowV g := originalSU2_row_v_zero_safe_polar g

/-- Both entries of the arbitrary ORIGINAL SU2 first row are
reproduced by the explicit original source ZYZ parameter values. -/
theorem original_source_zyz_firstRow (g : GaugeGroup 2)
    (j : Fin 2) :
    (sourceZYZMatrix
      (originalEulerLeftTime g)
      (originalEulerMiddleTime g)
      (originalEulerRightTime g)) 0 j = (g : ColorMatrix 2) 0 j := by
  fin_cases j
  · exact original_source_zyz_firstRow_u g
  · exact original_source_zyz_firstRow_v g

/-- Transport the checked first row back to multiplication of the
original positive-i SU2 color gauge transformations. -/
theorem original_source_zyz_gauge_firstRow (g : GaugeGroup 2)
    (j : Fin 2) :
    ((sourcePlusIGaugeCurve (2 : Fin 3) (originalEulerLeftTime g) *
      sourcePlusIGaugeCurve (1 : Fin 3) (originalEulerMiddleTime g) *
      sourcePlusIGaugeCurve (2 : Fin 3) (originalEulerRightTime g) :
        GaugeGroup 2) : ColorMatrix 2) 0 j =
      (g : ColorMatrix 2) 0 j := by
  rw [original_source_zyz_gauge_product_matrix]
  exact original_source_zyz_firstRow g j

#print axioms original_source_zyz_firstRow_u
#print axioms original_source_zyz_firstRow_v
#print axioms original_source_zyz_firstRow
#print axioms original_source_zyz_gauge_firstRow
#check @original_source_zyz_gauge_firstRow

end
end FCP.BFSSSU2PhysicalDomainL6H5E8X
