import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H3AOriginalSourceCorrelationKernelPointwiseProbe

/-!
L6H3B1 — exact ORIGINAL SU(2) BFSS Fock correlation's DOMINATION
PACKAGE. Source-typed genuine kernel from qualified L6H3A, actual
volume on Boson 2, original f : SmoothCore 2. Not an abstract Fock
surrogate. Isolate the concrete kernel hypotheses before any
dominated-convergence application.

#244 L6H3B timed out in 110s with NO elaborator error even though
its prerequisites were green; preserve this as negative knowledge.
This theorem establishes exactly the needed hypotheses in a
separate qualified .olean, but not the continuity of the integral.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 200000

namespace FCP.BFSSSU2PhysicalDomainL6H3B1
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H0
open FCP.BFSSSU2PhysicalDomainL6H2
open FCP.BFSSSU2PhysicalDomainL6H3A
open MeasureTheory

/-- A SINGLE integrable squared envelope bounds all literal BFSS
smooth SU(2) Fock-correlation kernels at fixed second parameter h.
In addition, the source kernel is AE-strongly measurable and
pointwise continuous in the first gauge parameter. -/
theorem actualOriginalSourceGaugeCorrelation_dominatedData
    (f : SmoothCore 2) (h : GaugeGroup 2) :
    ∃ B : Boson 2 → ℝ,
      Integrable B (volume : Measure (Boson 2)) ∧
      (∀ g : GaugeGroup 2,
        AEStronglyMeasurable
          (actualOriginalSourceGaugeCorrelationKernel f h g)
          (volume : Measure (Boson 2))) ∧
      (∀ g : GaugeGroup 2,
        ∀ᵐ x ∂(volume : Measure (Boson 2)),
          ‖actualOriginalSourceGaugeCorrelationKernel f h g x‖ ≤ B x) ∧
      ∀ᵐ x ∂(volume : Measure (Boson 2)),
        Continuous (fun g : GaugeGroup 2 =>
          actualOriginalSourceGaugeCorrelationKernel f h g x) := by
  obtain ⟨R, C, hR, hC, hIntegrable, hOrbitBound⟩ :=
    actualOriginalSmoothGaugeOrbit_integrableEnvelope f
  refine ⟨(fun x : Boson 2 =>
    (if ‖x‖ < R then C else 0) ^ 2), hIntegrable, ?_, ?_, ?_⟩
  · intro g
    exact actualOriginalSourceGaugeCorrelationKernel_aeMeasurable f h g
  · intro g
    exact Filter.Eventually.of_forall (fun x =>
      actualOriginalSourceGaugeCorrelationKernel_norm_le
        f R C hC hOrbitBound g h x)
  · exact Filter.Eventually.of_forall
      (actualOriginalSourceGaugeCorrelationKernel_continuous_g f h)

#print axioms actualOriginalSourceGaugeCorrelation_dominatedData
#check @actualOriginalSourceGaugeCorrelation_dominatedData

end
end FCP.BFSSSU2PhysicalDomainL6H3B1
