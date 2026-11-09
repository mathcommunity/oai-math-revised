import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E7BOriginalGaussFullL2ResidualIntegralBridgeProbe

/-!
L6H5E7C — GENUINE original BFSS FullL2 squared residual tends to
zero in real punctured time; derive strong Hilbert-space convergence.

Inputs are independently strict-qualified:
- H5E6C: original bosonic-volume integral of source exact Gauss
  quotient squared error tends to zero;
- H5E7B: exactly that integral equals the squared norm of the
  actual original FullL2 Gauss quotient residual, via AE equality.

The sole new analysis is an ABSTRACT fact about sqrt of squared
norms. No concrete Fock expression is re-elaborated, and the
original source +i SU2 action, signs, bosonic inverse pullback,
and right-ordered Gauss candidate are unchanged.

Generator domain and HasDerivAt still require a separately
qualified theorem. No spectral, closure or self-adjointness claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E7C
noncomputable section

open scoped Topology
open Filter
open MeasureTheory
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E6B
open FCP.BFSSSU2PhysicalDomainL6H5E6C
open FCP.BFSSSU2PhysicalDomainL6H5E7B

/-- At ANY filter, squared norm tending to zero is enough for
the vector to tend strongly to zero. This contains no BFSS or
source-specific Lean expressions. -/
theorem abstract_tendsto_zero_of_norm_sq_tendsto_zero
    {ι E : Type*} [NormedAddCommGroup E]
    {l : Filter ι} (v : ι → E)
    (hsq : Tendsto (fun a : ι => ‖v a‖ ^ 2) l (𝓝 (0 : ℝ))) :
    Tendsto v l (𝓝 (0 : E)) := by
  have hsqrt :
      Tendsto (fun a : ι => Real.sqrt (‖v a‖ ^ 2))
        l (𝓝 (Real.sqrt (0 : ℝ))) :=
    (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  have heq :
      (fun a : ι => Real.sqrt (‖v a‖ ^ 2)) =
      (fun a : ι => ‖v a‖) := by
    funext a
    exact Real.sqrt_sq (norm_nonneg (v a))
  rw [heq, Real.sqrt_zero] at hsqrt
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  simpa only [sub_zero] using hsqrt

/-- The ORIGINAL BFSS SU2 +i color orbit is strongly differentiable
on source SmoothCore in the precise sense that its FullL2
Gauss difference-quotient residual tends to zero in norm.
Formal HasDerivAt / generator domain conversion is the next leaf. -/
theorem actualOriginalGaussFullL2Residual_tendsto_zero
    (c : ColorIndex 2) (f : SmoothCore 2) :
    Tendsto (actualOriginalGaussFullL2Residual c f)
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : FullL2 2)) := by
  have hDCT :=
    actualOriginalGaussQuotientSquaredError_integral_tendsto_zero c f
  have heq :
      (fun t : ℝ => ‖actualOriginalGaussFullL2Residual c f t‖ ^ 2) =
      (fun t : ℝ =>
        ∫ x : Boson 2,
          actualOriginalGaussQuotientSquaredError c f t x
            ∂(volume : Measure (Boson 2))) := by
    funext t
    exact actualOriginalGaussFullL2Residual_norm_sq_eq_integral c f t
  have hsq :
      Tendsto
        (fun t : ℝ => ‖actualOriginalGaussFullL2Residual c f t‖ ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    rw [heq]
    exact hDCT
  exact abstract_tendsto_zero_of_norm_sq_tendsto_zero
    (actualOriginalGaussFullL2Residual c f) hsq

#print axioms abstract_tendsto_zero_of_norm_sq_tendsto_zero
#print axioms actualOriginalGaussFullL2Residual_tendsto_zero
#check @actualOriginalGaussFullL2Residual_tendsto_zero

end
end FCP.BFSSSU2PhysicalDomainL6H5E7C
