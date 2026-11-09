import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8XOriginalSU2SourceEulerFirstRowProbe

/-!
L6H5E8Y — original-source SU2 exact ZYZ Euler factorization.
Source conventions: ORIGINAL positive-i normalized Pauli +i
sourcePlusIGaugeCurve, original GaugeGroup 2, no surrogate action.

Strict accepted prerequisites:
H5E8Q original quaternion SU2 matrix form;
H5E8U original source ZYZ matrix identity;
H5E8V zero-safe quaternion row norm/polar;
H5E8W explicit original Pauli Euler times/phases;
H5E8X original-source first-row equality (#355).

This gate proves equality of ALL 2x2 entries, hence exact
factorization of each ORIGINAL GaugeGroup 2 element.
It does NOT claim generated-subgroup = top, joint Gauss
kernel equivalence, physical space, or spectral conclusions.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8Y
noncomputable section

open Matrix
open OAI.BFSSQuantum
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6H5E8Q
open FCP.BFSSSU2PhysicalDomainL6H5E8W
open FCP.BFSSSU2PhysicalDomainL6H5E8X

/-- For genuine original SU(2) color matrices, equality of
the first row implies equality of the full gauge-group elements.
The second row is forced by the formally accepted quaternion
matrix form; no analytic/group-generation hypothesis. -/
theorem originalSU2_eq_of_firstRow (g h : GaugeGroup 2)
    (hrow : ∀ j : Fin 2,
      (g : ColorMatrix 2) 0 j = (h : ColorMatrix 2) 0 j) :
    g = h := by
  apply Subtype.ext
  calc
    (g : ColorMatrix 2) =
      !![(g : ColorMatrix 2) 0 0, (g : ColorMatrix 2) 0 1;
         -star ((g : ColorMatrix 2) 0 1),
         star ((g : ColorMatrix 2) 0 0)] :=
           originalSU2_quaternion_matrix g
    _ =
      !![(h : ColorMatrix 2) 0 0, (h : ColorMatrix 2) 0 1;
         -star ((h : ColorMatrix 2) 0 1),
         star ((h : ColorMatrix 2) 0 0)] := by
           rw [hrow (0 : Fin 2), hrow (1 : Fin 2)]
    _ = (h : ColorMatrix 2) :=
      (originalSU2_quaternion_matrix h).symm

/-- Every GENUINE original SU2 gauge group element equals the
exact three ORIGINAL positive-i one-parameter color transformations,
with zero-safe explicit real Pauli times. -/
theorem original_source_zyz_exact_euler (g : GaugeGroup 2) :
    sourcePlusIGaugeCurve (2 : Fin 3) (originalEulerLeftTime g) *
      sourcePlusIGaugeCurve (1 : Fin 3) (originalEulerMiddleTime g) *
      sourcePlusIGaugeCurve (2 : Fin 3) (originalEulerRightTime g) = g := by
  apply originalSU2_eq_of_firstRow
  intro j
  exact original_source_zyz_gauge_firstRow g j

/-- Existence form, with the same *literal* original source
positive-i color one-parameter curves, not an alternative
Euler coordinate system or abstract subgroup. -/
theorem original_source_zyz_exists (g : GaugeGroup 2) :
    ∃ a b c : ℝ,
      sourcePlusIGaugeCurve (2 : Fin 3) a *
        sourcePlusIGaugeCurve (1 : Fin 3) b *
        sourcePlusIGaugeCurve (2 : Fin 3) c = g := by
  refine ⟨originalEulerLeftTime g, originalEulerMiddleTime g,
    originalEulerRightTime g, ?_⟩
  exact original_source_zyz_exact_euler g

#print axioms originalSU2_eq_of_firstRow
#print axioms original_source_zyz_exact_euler
#print axioms original_source_zyz_exists
#check @original_source_zyz_exact_euler

end
end FCP.BFSSSU2PhysicalDomainL6H5E8Y
