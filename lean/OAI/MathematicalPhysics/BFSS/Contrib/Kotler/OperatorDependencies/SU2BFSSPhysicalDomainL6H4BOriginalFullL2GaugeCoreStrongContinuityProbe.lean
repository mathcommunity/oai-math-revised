import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H4AOriginalFullL2GaugeCoreDistanceSqContinuityProbe

/-!
L6H4B — strong norm-topology continuity for ACTUAL original BFSS
FullL2 SU(2) gauge orbits of source SmoothCore vectors.

Only source-qualified H4A squared orbital distance continuity,
genuine original FullL2, and the pinned Mathlib sqrt/norm
topology are used. The full FullL2 extension via core density
is a SEPARATE, still-unqualified L6H4C target.

No new hypotheses, no Fock expansion, no change of signs, source
gauge representation, physical Hilbert space or operator domain.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H4B
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6H4A
open Filter

/-- Exact source gauge-orbit NORM distance is continuous in SU(2)
for every fixed smooth-core starting vector and gauge reference. -/
theorem actualOriginalFullL2GaugeCore_normDiff_continuous
    (f : SmoothCore 2) (h : GaugeGroup 2) :
    Continuous (fun g : GaugeGroup 2 =>
      ‖actualOriginalFullL2GaugePairCLM g (coreToL2 f) -
        actualOriginalFullL2GaugePairCLM h (coreToL2 f)‖) := by
  have hsqrt :
      Continuous (fun g : GaugeGroup 2 =>
        Real.sqrt
          (‖actualOriginalFullL2GaugePairCLM g (coreToL2 f) -
              actualOriginalFullL2GaugePairCLM h (coreToL2 f)‖ ^ 2)) :=
    Real.continuous_sqrt.comp
      (actualOriginalFullL2GaugeCore_distSq_continuous f h)
  have heq :
      (fun g : GaugeGroup 2 =>
        ‖actualOriginalFullL2GaugePairCLM g (coreToL2 f) -
          actualOriginalFullL2GaugePairCLM h (coreToL2 f)‖) =
      (fun g : GaugeGroup 2 =>
        Real.sqrt
          (‖actualOriginalFullL2GaugePairCLM g (coreToL2 f) -
              actualOriginalFullL2GaugePairCLM h (coreToL2 f)‖ ^ 2)) := by
    funext g
    symm
    exact Real.sqrt_sq (norm_nonneg _)
  rw [heq]
  exact hsqrt

/-- Genuine source BFSS SU(2) FullL2-valued gauge orbit is
strongly continuous for every original SmoothCore vector.
Extension to EVERY FullL2 vector remains a distinct density step. -/
theorem actualOriginalFullL2GaugeCore_orbit_continuous
    (f : SmoothCore 2) :
    Continuous (fun g : GaugeGroup 2 =>
      actualOriginalFullL2GaugePairCLM g (coreToL2 f)) := by
  apply continuous_iff_continuousAt.mpr
  intro h
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  simpa only [sub_self, norm_zero] using
    ((actualOriginalFullL2GaugeCore_normDiff_continuous f h).continuousAt (x := h)).tendsto

#print axioms actualOriginalFullL2GaugeCore_normDiff_continuous
#print axioms actualOriginalFullL2GaugeCore_orbit_continuous
#check @actualOriginalFullL2GaugeCore_orbit_continuous

end
end FCP.BFSSSU2PhysicalDomainL6H4B
