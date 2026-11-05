import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E1OriginalAllTimeGaussDerivativeIntegrableEnvelopeProbe
import Mathlib.Analysis.Calculus.MeanValue

/-!
L6H5E2 — difference bounds on the literal ORIGINAL source SU2 orbit
from the qualified all-time Gauss derivative and its integrable
envelope. The analytic mean-value inequality is proved first for
an abstract normed real vector space, not for concrete Fock data.

This leaf bounds finite-time differences, with a common squared-
integrable radial majorant; the quotient by nonzero time and the
actual FullL2 dominated-convergence limit are separate targets.
No new assumptions, no spectral or self-adjointness claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E2
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6H0
open FCP.BFSSSU2PhysicalDomainL6H5B
open FCP.BFSSSU2PhysicalDomainL6H5D3
open FCP.BFSSSU2PhysicalDomainL6H5E1
open MeasureTheory
open Set

/-- A generic real-parameter normed-space curve whose derivative
has global norm bound C is globally C-Lipschitz. In particular,
the proof does not unfold the 48-Majorana source representation. -/
theorem norm_orbit_difference_le_of_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (orbit deriv : ℝ → E) (C : ℝ)
    (hderiv : ∀ s : ℝ, HasDerivAt orbit (deriv s) s)
    (hbound : ∀ s : ℝ, ‖deriv s‖ ≤ C)
    (s t : ℝ) :
    ‖orbit t - orbit s‖ ≤ C * |t - s| := by
  rcases le_total s t with hst | hts
  · have hc : ContinuousOn orbit (Icc s t) :=
      fun z _ => (hderiv z).continuousAt.continuousWithinAt
    have hd : ∀ z ∈ Ico s t,
        HasDerivWithinAt orbit (deriv z) (Ici z) z :=
      fun z _ => (hderiv z).hasDerivWithinAt
    have h := norm_image_sub_le_of_norm_deriv_right_le_segment
      (a := s) (b := t) (f := orbit) (f' := deriv) (C := C)
      hc hd (fun z _ => hbound z) t (right_mem_Icc.mpr hst)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using h
  · have hc : ContinuousOn orbit (Icc t s) :=
      fun z _ => (hderiv z).continuousAt.continuousWithinAt
    have hd : ∀ z ∈ Ico t s,
        HasDerivWithinAt orbit (deriv z) (Ici z) z :=
      fun z _ => (hderiv z).hasDerivWithinAt
    have h := norm_image_sub_le_of_norm_deriv_right_le_segment
      (a := t) (b := s) (f := orbit) (f' := deriv) (C := C)
      hc hd (fun z _ => hbound z) s (right_mem_Icc.mpr hts)
    calc
      ‖orbit t - orbit s‖ = ‖orbit s - orbit t‖ := norm_sub_rev _ _
      _ ≤ C * (s - t) := h
      _ = C * |t - s| := by rw [abs_of_nonpos (sub_nonpos.mpr hts)]; ring

/-- The ORIGINAL source orbit has an integrably dominated
finite-time difference from its source time-zero state, for every
time and bosonic configuration. It is not a claim of FullL2
differentiability. -/
theorem actualOriginalGaussOrbit_difference_integrableEnvelope
    (c : ColorIndex 2) (f : SmoothCore 2) :
    ∃ (R C : ℝ), 0 < R ∧ 0 ≤ C ∧
      Integrable (fun x : Boson 2 =>
        (if ‖x‖ < R then C else 0) ^ 2)
        (volume : Measure (Boson 2)) ∧
      ∀ (t : ℝ) (x : Boson 2),
        ‖actualOriginalSmoothGaugeOrbitRepresentative f
            (sourcePlusIGaugeCurve c t) x -
          actualOriginalSmoothGaugeOrbitRepresentative f
            (sourcePlusIGaugeCurve c 0) x‖ ≤
          (if ‖x‖ < R then C else 0) * |t| := by
  obtain ⟨R, C, hR, hC, hint, hbound⟩ :=
    actualOriginalGaussOrbitDerivative_integrableEnvelope c f
  refine ⟨R, C, hR, hC, hint, ?_⟩
  intro t x
  let orbit : ℝ → Fermion 2 := fun s =>
    actualOriginalSmoothGaugeOrbitRepresentative f
      (sourcePlusIGaugeCurve c s) x
  let deriv : ℝ → Fermion 2 := fun s =>
    pairedGaugeData.fermion (sourcePlusIGaugeCurve c s)
      ((actualOriginalCoreColorGaussCandidate c f)
        (pairedGaugeData.boson (sourcePlusIGaugeCurve c s)⁻¹ x))
  have hd : ∀ s : ℝ, HasDerivAt orbit (deriv s) s := by
    intro s
    exact actualOriginalSmoothGaugeOrbit_colorCurve_hasDerivAt c f s x
  have hb : ∀ s : ℝ, ‖deriv s‖ ≤
      (if ‖x‖ < R then C else 0) := by
    intro s
    exact hbound s x
  -- Gate #286: the abstract mean-value inequality is axiom-clean.
  -- Only its final application failed: the expected bound has |t|
  -- while the applied lemma retains |t - 0|. Normalize that exact
  -- scalar expression, rather than unfolding source Fock operators.
  simpa only [sub_zero] using
    (norm_orbit_difference_le_of_derivative_bound orbit deriv
      (if ‖x‖ < R then C else 0) hd hb 0 t)

#print axioms norm_orbit_difference_le_of_derivative_bound
#print axioms actualOriginalGaussOrbit_difference_integrableEnvelope
#check @norm_orbit_difference_le_of_derivative_bound
#check @actualOriginalGaussOrbit_difference_integrableEnvelope

end
end FCP.BFSSSU2PhysicalDomainL6H5E2
