import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E6AOriginalGaussSquaredErrorDCTInterfaceProbe

/-!
L6H5E6B — source-exact, original-boson-volume domination DATA
for the squared error between the real SU2 difference quotient
and the source SmoothCore Gauss candidate D_c f.

The literal original Fock field appears only in a short named
integrand. Continuity in the original bosonic variable gives
AE strong measurability for each time; H5E5 provides a single
integrable bound on the squared error; H5E4 and the abstract
H5E6A norm-square limit give pointwise convergence.

This leaf deliberately DOES NOT yet apply dominated convergence
or claim FullL2 differentiation, generator-domain membership,
essential self-adjointness, or BFSS spectral conclusions.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E6B
noncomputable section

open scoped Topology
open Filter
open MeasureTheory
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6H0
open FCP.BFSSSU2PhysicalDomainL6H5B
open FCP.BFSSSU2PhysicalDomainL6H5E4
open FCP.BFSSSU2PhysicalDomainL6H5E5
open FCP.BFSSSU2PhysicalDomainL6H5E6A

/-- Source-exact scalar squared norm of the original real quotient's
difference from the +i color Gauss candidate, at a bosonic position. -/
def actualOriginalGaussQuotientSquaredError
    (c : ColorIndex 2) (f : SmoothCore 2) (t : ℝ)
    (x : Boson 2) : ℝ :=
  ‖(t⁻¹) •
    (actualOriginalSmoothGaugeOrbitRepresentative f
       (sourcePlusIGaugeCurve c t) x -
     actualOriginalSmoothGaugeOrbitRepresentative f
       (sourcePlusIGaugeCurve c 0) x) -
    (actualOriginalCoreColorGaussCandidate c f) x‖ ^ 2

/-- Continuity in the genuine original 27-dimensional bosonic
variable, hence measurability in the native original volume. -/
theorem actualOriginalGaussQuotientSquaredError_continuous_x
    (c : ColorIndex 2) (f : SmoothCore 2) (t : ℝ) :
    Continuous (actualOriginalGaussQuotientSquaredError c f t) := by
  have hsection (g : GaugeGroup 2) :
      Continuous (fun x : Boson 2 =>
        actualOriginalSmoothGaugeOrbitRepresentative f g x) := by
    have hp : Continuous (fun x : Boson 2 => (g, x)) :=
      continuous_const.prodMk continuous_id
    have hc := (actualOriginalSmoothGaugeOrbit_jointContinuous f).comp hp
    change Continuous (fun x : Boson 2 =>
      actualOriginalSmoothGaugeOrbitRepresentative f g x) at hc
    exact hc
  -- #300 first error: pin the REAL inverse-time scalar before
  -- continuous smul; otherwise Lean leaves its scalar metavariable open.
  have hscalar : Continuous (fun _ : Boson 2 => (t⁻¹ : ℝ)) :=
    continuous_const
  have hquot : Continuous (fun x : Boson 2 =>
      (t⁻¹) •
        (actualOriginalSmoothGaugeOrbitRepresentative f
            (sourcePlusIGaugeCurve c t) x -
          actualOriginalSmoothGaugeOrbitRepresentative f
            (sourcePlusIGaugeCurve c 0) x)) :=
    hscalar.smul
      ((hsection (sourcePlusIGaugeCurve c t)).sub
        (hsection (sourcePlusIGaugeCurve c 0)))
  have herror := (hquot.sub
    (actualOriginalCoreColorGaussCandidate c f).continuous).norm.pow 2
  change Continuous (actualOriginalGaussQuotientSquaredError c f t) at herror
  exact herror

/-- All original SU2 squared-error sections are AE-strongly
measurable with respect to the ORIGINAL bosonic volume. -/
theorem actualOriginalGaussQuotientSquaredError_aeMeasurable
    (c : ColorIndex 2) (f : SmoothCore 2) (t : ℝ) :
    AEStronglyMeasurable
      (actualOriginalGaussQuotientSquaredError c f t)
      (volume : Measure (Boson 2)) :=
  (actualOriginalGaussQuotientSquaredError_continuous_x c f t).aestronglyMeasurable

/-- Exact original source squared-error data packaged without
asking Lean to elaborate a concrete integral or FullL2 bridge. -/
theorem actualOriginalGaussQuotientSquaredError_dominatedData
    (c : ColorIndex 2) (f : SmoothCore 2) :
    ∃ B : Boson 2 → ℝ,
      Integrable B (volume : Measure (Boson 2)) ∧
      (∀ t : ℝ,
        AEStronglyMeasurable
          (actualOriginalGaussQuotientSquaredError c f t)
          (volume : Measure (Boson 2))) ∧
      (∀ t : ℝ, t ≠ 0 → ∀ x : Boson 2,
        ‖actualOriginalGaussQuotientSquaredError c f t x‖ ≤ B x) ∧
      (∀ x : Boson 2,
        Tendsto (fun t : ℝ => actualOriginalGaussQuotientSquaredError c f t x)
          (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ))) := by
  obtain ⟨R, C, hR, hC, hint, hbound⟩ :=
    actualOriginalGaussOrbit_quotientError_sqIntegrableEnvelope c f
  refine ⟨(fun x : Boson 2 =>
    (2 * (if ‖x‖ < R then C else 0)) ^ 2), hint, ?_, ?_, ?_⟩
  · intro t
    exact actualOriginalGaussQuotientSquaredError_aeMeasurable c f t
  · intro t ht x
    -- #300 second error: name the source error as an opaque Fock
    -- vector, square its norm, then normalize the Real norm with an
    -- explicitly typed nonnegativity witness.
    let e : Fermion 2 :=
      (t⁻¹) •
        (actualOriginalSmoothGaugeOrbitRepresentative f
            (sourcePlusIGaugeCurve c t) x -
          actualOriginalSmoothGaugeOrbitRepresentative f
            (sourcePlusIGaugeCurve c 0) x) -
        (actualOriginalCoreColorGaussCandidate c f) x
    have herr : ‖e‖ ≤ 2 * (if ‖x‖ < R then C else 0) :=
      hbound t ht x
    have hsq : ‖e‖ ^ 2 ≤
        (2 * (if ‖x‖ < R then C else 0)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg e) herr 2
    have hnonneg : (0 : ℝ) ≤ ‖e‖ ^ 2 := sq_nonneg (‖e‖)
    change ‖(‖e‖ ^ 2 : ℝ)‖ ≤
      (2 * (if ‖x‖ < R then C else 0)) ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hsq
  · intro x
    have hlim := actualOriginalGaussOrbit_differenceQuotient_pointwise_tendsto c f x
    have hsquared :=
      norm_sub_sq_tendsto_zero_of_tendsto
        (fun t : ℝ =>
          (t⁻¹) •
            (actualOriginalSmoothGaugeOrbitRepresentative f
              (sourcePlusIGaugeCurve c t) x -
             actualOriginalSmoothGaugeOrbitRepresentative f
              (sourcePlusIGaugeCurve c 0) x))
        ((actualOriginalCoreColorGaussCandidate c f) x) hlim
    change Tendsto
      (fun t : ℝ => actualOriginalGaussQuotientSquaredError c f t x)
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) at hsquared
    exact hsquared

#print axioms actualOriginalGaussQuotientSquaredError
#print axioms actualOriginalGaussQuotientSquaredError_continuous_x
#print axioms actualOriginalGaussQuotientSquaredError_aeMeasurable
#print axioms actualOriginalGaussQuotientSquaredError_dominatedData
#check @actualOriginalGaussQuotientSquaredError_dominatedData

end
end FCP.BFSSSU2PhysicalDomainL6H5E6B
