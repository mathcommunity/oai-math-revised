import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H1ActualOriginalSmoothGaugeUniformEnvelopeProbe

/-!
L6H2 — the native original BFSS bosonic volume has finite measure
on every finite-radius open ball, so the proven uniform compact
support envelope of L6H1 and its square are integrable.

No new measure, no replacement Hilbert space and no source signs
changed. This is the precise domination input needed for genuine
L² strong continuity of the source SU(2) action. That continuity
itself is NOT asserted by this file.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace FCP.BFSSSU2PhysicalDomainL6H2
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H1
open FCP.BFSSSU2PhysicalDomainL6H0
open MeasureTheory

/-- Balls of the original 27-coordinate bosonic Euclidean space
have finite original volume, even though the entire space does not. -/
theorem actualOriginalBosonBall_finiteMeasure (R : ℝ) :
    (volume : Measure (Boson 2)) (Metric.ball 0 R) < ⊤ := by
  -- Pinned Mathlib: bounded balls have finite volume in the original
  -- finite-dimensional Euclidean bosonic configuration space.
  exact measure_ball_lt_top

/-- Integrability of the actual fixed-support scalar envelope
against the original bosonic Lebesgue volume. -/
theorem actualOriginalRadialEnvelope_integrable (R C : ℝ) :
    Integrable (fun x : Boson 2 => if ‖x‖ < R then C else 0)
      (volume : Measure (Boson 2)) := by
  classical
  let s : Set (Boson 2) := Metric.ball 0 R
  have hs : MeasurableSet s := Metric.isOpen_ball.measurableSet
  have hfinite : (volume : Measure (Boson 2)) s ≠ ⊤ :=
    (actualOriginalBosonBall_finiteMeasure R).ne
  have hconst : IntegrableOn (fun _ : Boson 2 => C) s
      (volume : Measure (Boson 2)) :=
    integrableOn_const hfinite
  have hint := hconst.integrable_indicator hs
  have heq :
      (fun x : Boson 2 => if ‖x‖ < R then C else 0) =
        Set.indicator s (fun _ : Boson 2 => C) := by
    funext x
    simp [Set.indicator, s, Metric.mem_ball, dist_zero_right]
  rw [heq]
  exact hint

/-- L² domination requires integrability of the envelope SQUARED;
this is independently discharged by the same finite-volume ball. -/
theorem actualOriginalRadialEnvelope_sq_integrable (R C : ℝ) :
    Integrable (fun x : Boson 2 =>
      (if ‖x‖ < R then C else 0) ^ 2)
      (volume : Measure (Boson 2)) := by
  have heq :
      (fun x : Boson 2 => (if ‖x‖ < R then C else 0) ^ 2) =
        (fun x : Boson 2 => if ‖x‖ < R then C ^ 2 else 0) := by
    funext x
    split_ifs <;> simp
  rw [heq]
  exact actualOriginalRadialEnvelope_integrable R (C ^ 2)

/-- Integrable bound for EVERY literal source-gauge image of an
original SmoothCore state. Does NOT itself prove norm continuity. -/
theorem actualOriginalSmoothGaugeOrbit_integrableEnvelope
    (f : SmoothCore 2) :
    ∃ (R C : ℝ), 0 < R ∧ 0 ≤ C ∧
      Integrable (fun x : Boson 2 =>
        (if ‖x‖ < R then C else 0) ^ 2)
        (volume : Measure (Boson 2)) ∧
      ∀ (g : GaugeGroup 2) (x : Boson 2),
        ‖actualOriginalSmoothGaugeOrbitRepresentative f g x‖ ≤
          if ‖x‖ < R then C else 0 := by
  obtain ⟨R, C, hR, hC, hbound⟩ :=
    actualOriginalSmoothGaugeOrbit_uniformEnvelope f
  exact ⟨R, C, hR, hC,
    actualOriginalRadialEnvelope_sq_integrable R C, hbound⟩

#print axioms actualOriginalBosonBall_finiteMeasure
#print axioms actualOriginalRadialEnvelope_integrable
#print axioms actualOriginalRadialEnvelope_sq_integrable
#print axioms actualOriginalSmoothGaugeOrbit_integrableEnvelope
#check @actualOriginalSmoothGaugeOrbit_integrableEnvelope

end
end FCP.BFSSSU2PhysicalDomainL6H2
