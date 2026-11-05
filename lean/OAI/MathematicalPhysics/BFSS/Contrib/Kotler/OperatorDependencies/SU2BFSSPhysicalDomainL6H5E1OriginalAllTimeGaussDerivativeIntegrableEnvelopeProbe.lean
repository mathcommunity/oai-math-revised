import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5D3OriginalGaussCurveAllTimePointwiseDerivativeProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H2ActualOriginalSmoothGaugeIntegrableEnvelopeProbe

/-!
L6H5E1 — a common original-boson-volume integrable envelope
for the exact derivative of the ORIGINAL BFSS source SU2 orbit
at ALL real times. No bound on a divided difference is assumed.

The H5D3 derivative is exactly the original gauge orbit of
D_c f, and H5B makes D_c f a *genuine SmoothCore 2*.
Thus H1/H2's already-qualified source all-gauge compact-support
and squared-integrability estimates apply directly to D_c f.

This does NOT establish FullL2 differentiation or domination of
difference quotients. That requires an independently justified
finite-dimensional mean-value bound, followed by dominated
convergence for the original full-L2 a.e. representatives.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E1
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6H0
open FCP.BFSSSU2PhysicalDomainL6H2
open FCP.BFSSSU2PhysicalDomainL6H5B
open FCP.BFSSSU2PhysicalDomainL6H5D3
open MeasureTheory

/-- The *actual pointwise source Gauss derivative* is bounded by
the same squared-integrable radial majorant at every time,
using H2 on the genuine source SmoothCore element D_c f. -/
theorem actualOriginalGaussOrbitDerivative_integrableEnvelope
    (c : ColorIndex 2) (f : SmoothCore 2) :
    ∃ (R C : ℝ), 0 < R ∧ 0 ≤ C ∧
      Integrable (fun x : Boson 2 =>
        (if ‖x‖ < R then C else 0) ^ 2)
        (volume : Measure (Boson 2)) ∧
      ∀ (t : ℝ) (x : Boson 2),
        ‖pairedGaugeData.fermion (sourcePlusIGaugeCurve c t)
          ((actualOriginalCoreColorGaussCandidate c f)
            (pairedGaugeData.boson (sourcePlusIGaugeCurve c t)⁻¹ x))‖ ≤
        if ‖x‖ < R then C else 0 := by
  obtain ⟨R, C, hR, hC, hint, hbound⟩ :=
    actualOriginalSmoothGaugeOrbit_integrableEnvelope
      (actualOriginalCoreColorGaussCandidate c f)
  refine ⟨R, C, hR, hC, hint, ?_⟩
  intro t x
  -- Rewrite only the short H0 representative definition; do NOT
  -- unfold pairedGaugeData's concrete six-field Fock implementation.
  change
    ‖actualOriginalSmoothGaugeOrbitRepresentative
      (actualOriginalCoreColorGaussCandidate c f)
      (sourcePlusIGaugeCurve c t) x‖ ≤
        if ‖x‖ < R then C else 0
  exact hbound (sourcePlusIGaugeCurve c t) x

#print axioms actualOriginalGaussOrbitDerivative_integrableEnvelope
#check @actualOriginalGaussOrbitDerivative_integrableEnvelope

end
end FCP.BFSSSU2PhysicalDomainL6H5E1
