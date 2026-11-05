import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E6BOriginalGaussSquaredErrorDominatedDataProbe

/-!
L6H5E6C — original source SU2 Gauss squared-error Bochner integral
converges to zero along the REAL punctured-time filter.

This is the application of the independently kernel-qualified
H5E6A source-volume dominated-convergence interface to the
H5E6B source-exact dominated-data package. The ORIGINAL
48-Majorana Fock action and inverse bosonic SU2 pullback remain
sealed inside previously-qualified .olean declarations.

This theorem is about the literal integrals against original
Boson 2 volume. It does NOT yet identify the integral with
a FullL2 norm square or establish generator-domain membership.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E6C
noncomputable section

open scoped Topology
open Filter
open MeasureTheory
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E6A
open FCP.BFSSSU2PhysicalDomainL6H5E6B

/-- The exact original SU2 squared Gauss difference-quotient error
has original bosonic-volume integral tending to zero as time
approaches zero through nonzero real values. -/
theorem actualOriginalGaussQuotientSquaredError_integral_tendsto_zero
    (c : ColorIndex 2) (f : SmoothCore 2) :
    Tendsto
      (fun t : ℝ =>
        ∫ x : Boson 2, actualOriginalGaussQuotientSquaredError c f t x
          ∂(volume : Measure (Boson 2)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  obtain ⟨B, hint, hmeas, hbound, hlim⟩ :=
    actualOriginalGaussQuotientSquaredError_dominatedData c f
  exact originalBosonVolume_puncturedDCT_squaredError
    (actualOriginalGaussQuotientSquaredError c f)
    B hmeas hbound hint hlim

#print axioms actualOriginalGaussQuotientSquaredError_integral_tendsto_zero
#check @actualOriginalGaussQuotientSquaredError_integral_tendsto_zero

end
end FCP.BFSSSU2PhysicalDomainL6H5E6C
