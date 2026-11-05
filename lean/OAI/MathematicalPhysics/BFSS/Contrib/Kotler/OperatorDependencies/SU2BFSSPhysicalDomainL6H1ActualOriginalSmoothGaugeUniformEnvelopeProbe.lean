import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H0OriginalSmoothGaugeOrbitRepresentativeProbe

/-!
L6H1 — the ORIGINAL BFSS smooth-core SU(2) gauge orbit has
a COMMON COMPACT-SUPPORT RADIUS and a UNIFORM integrable-envelope
candidate, independently of the gauge-group parameter.

This uses the true original SmoothCore f : TestFunction, the
pinned Mathlib compact-support lemmas, the source bosonic
LinearIsometryEquiv norm_map, and the actual fermionic isometry.
No new assumptions and NO replacement gauge map.

This gate proves *pointwise* support and uniform bounds only.
It does NOT establish integrability of the ball indicator,
L2 dominated convergence, full Hilbert strong continuity or
the Gauss-generator domain. Those are distinct next steps.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace FCP.BFSSSU2PhysicalDomainL6H1
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6H0

/-- ORIGINAL compact support plus ORIGINAL bosonic gauge
norm-isometry gives a common radius for ALL SU(2) transforms. -/
theorem actualOriginalSmoothGaugeOrbit_uniformSupport
    (f : SmoothCore 2) :
    ∃ R : ℝ, 0 < R ∧
      ∀ (g : GaugeGroup 2) (x : Boson 2), R ≤ ‖x‖ →
        actualOriginalSmoothGaugeOrbitRepresentative f g x = 0 := by
  obtain ⟨R, hR, houtside⟩ :=
    f.hasCompactSupport.exists_pos_le_norm
  refine ⟨R, hR, ?_⟩
  intro g x hx
  have hnorm : ‖pairedGaugeData.boson g⁻¹ x‖ = ‖x‖ :=
    (pairedGaugeData.boson g⁻¹).norm_map _
  have hzero : f (pairedGaugeData.boson g⁻¹ x) = 0 :=
    houtside _ (by simpa only [hnorm] using hx)
  -- #234: unrestricted simp normalizes boson g⁻¹ into (boson g).symm
  -- before using hzero, so the verified source equality fails to match.
  -- Keep the original GaugeCore action in precisely its source syntax.
  change pairedGaugeData.fermion g
    (f (pairedGaugeData.boson g⁻¹ x)) = 0
  simpa only [hzero, map_zero]

/-- Uniform pointwise amplitude bound independent of g and x;
the original fermion action preserves the source Fock norm. -/
theorem actualOriginalSmoothGaugeOrbit_uniformNorm
    (f : SmoothCore 2) :
    ∃ C : ℝ, ∀ (g : GaugeGroup 2) (x : Boson 2),
      ‖actualOriginalSmoothGaugeOrbitRepresentative f g x‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  refine ⟨C, ?_⟩
  intro g x
  rw [actualOriginalSmoothGaugeOrbit_norm]
  exact hC _

/-- A single compactly supported (closed-ball) measurable-majorant
candidate dominates EVERY source smooth-core gauge orbit.
Its integration is NOT asserted in this gate. -/
theorem actualOriginalSmoothGaugeOrbit_uniformEnvelope
    (f : SmoothCore 2) :
    ∃ (R C : ℝ), 0 < R ∧ 0 ≤ C ∧
      ∀ (g : GaugeGroup 2) (x : Boson 2),
        ‖actualOriginalSmoothGaugeOrbitRepresentative f g x‖ ≤
          if ‖x‖ < R then C else 0 := by
  obtain ⟨R, hR, hvanish⟩ :=
    actualOriginalSmoothGaugeOrbit_uniformSupport f
  obtain ⟨C, hC⟩ :=
    actualOriginalSmoothGaugeOrbit_uniformNorm f
  refine ⟨R, max C 0, hR, le_max_right _ _, ?_⟩
  intro g x
  split_ifs with hx
  · exact (hC g x).trans (le_max_left _ _)
  · have hv := hvanish g x (le_of_not_gt hx)
    simp [hv]

#print axioms actualOriginalSmoothGaugeOrbit_uniformSupport
#print axioms actualOriginalSmoothGaugeOrbit_uniformNorm
#print axioms actualOriginalSmoothGaugeOrbit_uniformEnvelope
#check @actualOriginalSmoothGaugeOrbit_uniformEnvelope

end
end FCP.BFSSSU2PhysicalDomainL6H1
