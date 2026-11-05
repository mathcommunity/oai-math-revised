import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H2TOriginalSU2FirstCountableProbe

/-!
L6H2U — an OPAQUE named dominated-convergence interface for the exact
original SU(2) gauge parameter and native Boson 2 volume.

Key negative knowledge: #239/#241 runner shutdowns occurred while
checking the enormous concrete L6H3 continuous_of_dominated call,
despite the mathematically independent components having compiled.
#241 qualified first countability, so the topology obligation is
resolved. We now compile this abstract but source-typed continuity
lemma before inserting any concrete fermionic/Fock expression.

This is pure Mathlib dominated convergence; the only specialized
objects are the ORIGINAL SU(2) parameter and Boson 2 volume.
NO new axiom, surrogate action, or physical conclusion.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSSU2PhysicalDomainL6H2U
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2PhysicalDomainL6H2T
open MeasureTheory

/-- Source-typed continuity of complex Bochner integrals under one
fixed integrable real majorant, with the original matrix-subtype
first-countability already proved in L6H2T. -/
theorem actualOriginalSU2_continuous_integral_of_dominated
    (F : GaugeGroup 2 → Boson 2 → ℂ)
    (bound : Boson 2 → ℝ)
    (hFmeas : ∀ g : GaugeGroup 2,
      AEStronglyMeasurable (F g) (volume : Measure (Boson 2)))
    (hbound : ∀ g : GaugeGroup 2,
      ∀ᵐ x ∂(volume : Measure (Boson 2)), ‖F g x‖ ≤ bound x)
    (hint : Integrable bound (volume : Measure (Boson 2)))
    (hcont : ∀ᵐ x ∂(volume : Measure (Boson 2)),
      Continuous (fun g : GaugeGroup 2 => F g x)) :
    Continuous (fun g : GaugeGroup 2 =>
      ∫ x : Boson 2, F g x ∂(volume : Measure (Boson 2))) := by
  letI : FirstCountableTopology (GaugeGroup 2) :=
    actualOriginalSU2_firstCountable
  exact continuous_of_dominated hFmeas hbound hint hcont

#print axioms actualOriginalSU2_continuous_integral_of_dominated
#check @actualOriginalSU2_continuous_integral_of_dominated

end
end FCP.BFSSSU2PhysicalDomainL6H2U
