import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H3B1OriginalSourceCorrelationDominationDataProbe

/-!
L6H3B2 — exact original BFSS source SU2 correlation integral
continuity, connecting TWO ALREADY QUALIFIED compiled constants.

L6H3B1: single source-integrable domination package for the actual
original paired BFSS Fock inner-correlation kernel; gate #245 GREEN.
L6H2U: source-typed abstract dominated-convergence theorem;
gate #242 isolated lemma GREEN with accepted axiom audit.

Important negative knowledge: #244 repeatedly elaborated the
concrete kernel/hypotheses in the same theorem and timed out at
110s. This file intentionally keeps a two-lemma proof and no
simplification/unfolding of the source fermionic Fock action.
No new axiom, Hilbert surrogate, sign or inverse convention change.
-/

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 120000

namespace FCP.BFSSSU2PhysicalDomainL6H3B2
noncomputable section
open OAI.BFSSQuantum
open FCP.BFSSSU2PhysicalDomainL6H3A
open FCP.BFSSSU2PhysicalDomainL6H3B1
open MeasureTheory

/-- Actual original 2×2 SU2 source gauge smooth-core correlation
is continuous after integrating in original 27-coordinate volume.
The source Fock/kernel proof is already cached in the imported
H3B1 lemma; no full Fock elaboration is requested here. -/
theorem actualOriginalSourceGaugeCorrelationIntegral_continuous
    (f : SmoothCore 2) (h : GaugeGroup 2) :
    Continuous (fun g : GaugeGroup 2 =>
      ∫ x : Boson 2,
        actualOriginalSourceGaugeCorrelationKernel f h g x
        ∂(volume : Measure (Boson 2))) := by
  obtain ⟨B, hint, hmeas, hbound, hcont⟩ :=
    actualOriginalSourceGaugeCorrelation_dominatedData f h
  exact
    FCP.BFSSSU2PhysicalDomainL6H2U.actualOriginalSU2_continuous_integral_of_dominated
      (actualOriginalSourceGaugeCorrelationKernel f h) B
      hmeas hbound hint hcont

#print axioms actualOriginalSourceGaugeCorrelationIntegral_continuous
#check @actualOriginalSourceGaugeCorrelationIntegral_continuous

end
end FCP.BFSSSU2PhysicalDomainL6H3B2
