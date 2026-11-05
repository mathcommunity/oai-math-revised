import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H3B2OriginalSourceCorrelationIntegralContinuityProbe

/-!
L6H3C — actual source BFSS Hilbert inner product equals the
already-qualified original gauge-correlation kernel integral;
therefore it is continuous in the SU(2) parameter.

Inputs ONLY:
* H0 accepted AE identification of literal original FullL2 gauge
  action on coreToL2 f with source original SmoothCore orbit.
* Mathlib L2.inner_def, unchanged original Boson 2 volume.
* H3B2 accepted source complex gauge-correlation integral continuity
  (strict axiom-qualified at Original Source Spin Identity #246).

No monolithic dominated convergence or concrete Fock action
elaboration. FullL2 strong NORM continuity and density extension
are NOT claimed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 180000

namespace FCP.BFSSSU2PhysicalDomainL6H3C
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H0
open FCP.BFSSSU2PhysicalDomainL6H3A
open FCP.BFSSSU2PhysicalDomainL6H3B2
open FCP.BFSSSU2PhysicalDomainL6G7U
open MeasureTheory

/-- EXACT native FullL2 complex inner product of the original
BFSS SU(2) unitary gauge orbit equals the source correlation
integral already proved continuous in H3B2. -/
theorem actualOriginalFullL2GaugeCore_inner_eq_correlationIntegral
    (f : SmoothCore 2) (g h : GaugeGroup 2) :
    inner ℂ (actualOriginalFullL2GaugePairCLM g (coreToL2 f))
      (actualOriginalFullL2GaugePairCLM h (coreToL2 f)) =
    ∫ x : Boson 2,
      actualOriginalSourceGaugeCorrelationKernel f h g x
      ∂(volume : Measure (Boson 2)) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [actualOriginalSmoothGaugeOrbit_ae_fullL2 f g,
      actualOriginalSmoothGaugeOrbit_ae_fullL2 f h] with x hg hh
  dsimp only [actualOriginalSourceGaugeCorrelationKernel]
  rw [hg, hh]

/-- Genuine ORIGINAL FullL2 BFSS SU(2) Hilbert matrix
coefficient is continuous at every source gauge parameter,
for smooth-core vectors. This is not yet strong continuity. -/
theorem actualOriginalFullL2GaugeCore_innerContinuous
    (f : SmoothCore 2) (h : GaugeGroup 2) :
    Continuous (fun g : GaugeGroup 2 =>
      inner ℂ (actualOriginalFullL2GaugePairCLM g (coreToL2 f))
        (actualOriginalFullL2GaugePairCLM h (coreToL2 f))) := by
  have heq :
      (fun g : GaugeGroup 2 =>
        inner ℂ (actualOriginalFullL2GaugePairCLM g (coreToL2 f))
          (actualOriginalFullL2GaugePairCLM h (coreToL2 f))) =
      (fun g : GaugeGroup 2 =>
        ∫ x : Boson 2,
          actualOriginalSourceGaugeCorrelationKernel f h g x
          ∂(volume : Measure (Boson 2))) := by
    funext g
    exact actualOriginalFullL2GaugeCore_inner_eq_correlationIntegral f g h
  rw [heq]
  exact actualOriginalSourceGaugeCorrelationIntegral_continuous f h

#print axioms actualOriginalFullL2GaugeCore_inner_eq_correlationIntegral
#print axioms actualOriginalFullL2GaugeCore_innerContinuous
#check @actualOriginalFullL2GaugeCore_innerContinuous

end
end FCP.BFSSSU2PhysicalDomainL6H3C
