import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E4OriginalGaussDifferenceQuotientPointwiseLimitProbe

/-!
L6H5E5 — integrable squared-error domination of the ORIGINAL
SU2 Gauss difference quotient about the original source Gauss
candidate. H5E3 gives a uniform square-integrable bound on the
quotient; H5E4 proves its pointwise limit is exactly D_c f.

We FIRST prove the closed-norm bound on a generic real-parameter
normed vector-valued curve. Only then do we specialize to the
actual original 48-Majorana Fock fiber. The residual majorant is
(2 E(x))^2 = 4 E(x)^2, integrable by the existing H5E3 estimate.

This is still a POINTWISE error/envelope theorem. FullL2 norm
convergence, generator-domain identification and any BFSS spectrum
claim require additional original-a.e. and dominated-integral steps.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E5
noncomputable section

open scoped Topology
open Filter
open MeasureTheory
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6H0
open FCP.BFSSSU2PhysicalDomainL6H5B
open FCP.BFSSSU2PhysicalDomainL6H5E3
open FCP.BFSSSU2PhysicalDomainL6H5E4

/-- If every nonzero-time quotient has norm ≤ C, its punctured
limit also has norm ≤ C, and the error is bounded by 2 C.
No concrete group/Fock expression occurs in the proof. -/
theorem norm_error_le_two_majorant_of_punctured_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℝ → E) (v : E) (C : ℝ)
    (hlim : Tendsto q (𝓝[≠] (0 : ℝ)) (𝓝 v))
    (hbound : ∀ t : ℝ, t ≠ 0 → ‖q t‖ ≤ C)
    (t : ℝ) (ht : t ≠ 0) :
    ‖q t - v‖ ≤ 2 * C := by
  have hv : ‖v‖ ≤ C := by
    apply le_of_tendsto hlim.norm
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hbound s (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs)
  calc
    ‖q t - v‖ ≤ ‖q t‖ + ‖v‖ := norm_sub_le _ _
    _ ≤ C + C := add_le_add (hbound t ht) hv
    _ = 2 * C := by ring

/-- Exact source Gauss quotient error, dominated in real Fock norm
by TWICE one common radial majorant whose square is integrable
against genuine original bosonic volume. The pointwise limit is
the original D_c f, with the original +i gauge curve unchanged. -/
theorem actualOriginalGaussOrbit_quotientError_sqIntegrableEnvelope
    (c : ColorIndex 2) (f : SmoothCore 2) :
    ∃ (R C : ℝ), 0 < R ∧ 0 ≤ C ∧
      Integrable (fun x : Boson 2 =>
        (2 * (if ‖x‖ < R then C else 0)) ^ 2)
        (volume : Measure (Boson 2)) ∧
      ∀ (t : ℝ), t ≠ 0 → ∀ (x : Boson 2),
        ‖(t⁻¹) •
          (actualOriginalSmoothGaugeOrbitRepresentative f
              (sourcePlusIGaugeCurve c t) x -
            actualOriginalSmoothGaugeOrbitRepresentative f
              (sourcePlusIGaugeCurve c 0) x) -
            ((actualOriginalCoreColorGaussCandidate c f) x)‖ ≤
          2 * (if ‖x‖ < R then C else 0) := by
  obtain ⟨R, C, hR, hC, hint, hquot⟩ :=
    actualOriginalGaussOrbit_differenceQuotient_integrableEnvelope c f
  have hsquare :
      (fun x : Boson 2 => (2 * (if ‖x‖ < R then C else 0)) ^ 2) =
      (fun x : Boson 2 => 4 * (if ‖x‖ < R then C else 0) ^ 2) := by
    funext x
    ring
  have htwice : Integrable
      (fun x : Boson 2 => (2 * (if ‖x‖ < R then C else 0)) ^ 2)
      (volume : Measure (Boson 2)) := by
    rw [hsquare]
    exact hint.const_mul (4 : ℝ)
  refine ⟨R, C, hR, hC, htwice, ?_⟩
  intro t ht x
  let q : ℝ → Fermion 2 := fun s =>
    (s⁻¹) •
      (actualOriginalSmoothGaugeOrbitRepresentative f
          (sourcePlusIGaugeCurve c s) x -
        actualOriginalSmoothGaugeOrbitRepresentative f
          (sourcePlusIGaugeCurve c 0) x)
  let v : Fermion 2 := (actualOriginalCoreColorGaussCandidate c f) x
  have hlim : Tendsto q (𝓝[≠] (0 : ℝ)) (𝓝 v) :=
    actualOriginalGaussOrbit_differenceQuotient_pointwise_tendsto c f x
  have hb : ∀ s : ℝ, s ≠ 0 →
      ‖q s‖ ≤ if ‖x‖ < R then C else 0 := by
    intro s hs
    exact hquot s hs x
  change ‖q t - v‖ ≤ 2 * (if ‖x‖ < R then C else 0)
  exact norm_error_le_two_majorant_of_punctured_limit q v
    (if ‖x‖ < R then C else 0) hlim hb t ht

#print axioms norm_error_le_two_majorant_of_punctured_limit
#print axioms actualOriginalGaussOrbit_quotientError_sqIntegrableEnvelope
#check @norm_error_le_two_majorant_of_punctured_limit
#check @actualOriginalGaussOrbit_quotientError_sqIntegrableEnvelope

end
end FCP.BFSSSU2PhysicalDomainL6H5E5
