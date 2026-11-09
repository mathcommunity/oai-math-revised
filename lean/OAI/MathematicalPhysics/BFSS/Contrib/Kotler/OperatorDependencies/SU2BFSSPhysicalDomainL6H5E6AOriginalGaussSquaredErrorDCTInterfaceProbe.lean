import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E5OriginalGaussQuotientErrorSquaredEnvelopeProbe
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
L6H5E6A — the exact original bosonic-volume, punctured-zero
dominated-convergence INTERFACE for squared Gauss quotient error.

Keep the Bochner integral limit abstract in its scalar integrand;
the pinned Mathlib dominated convergence theorem only needs:
(a) a.e. strongly measurable scalar error for each t,
(b) one integrable majorant, (c) a.e. pointwise convergence.

The qualified H5E4 proves the exact original Gauss quotient's
pointwise convergence. H5E5 supplies the majorant; these will be
assembled with the genuine source measurability in subsequent leaves.

NO claim of original FullL2 norm differentiation or generator-domain
identification is made by this abstract source-volume interface.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E6A
noncomputable section

open scoped Topology
open Filter
open MeasureTheory
open OAI.BFSSQuantum

/-- The pinned Mathlib filter-dominated convergence theorem, at
the REAL punctured-zero filter and original Boson 2 volume.
The Fock-dependent integrand is deliberately kept opaque. -/
theorem originalBosonVolume_puncturedDCT_squaredError
    (F : ℝ → Boson 2 → ℝ) (B : Boson 2 → ℝ)
    (hmeas : ∀ t : ℝ,
      AEStronglyMeasurable (F t) (volume : Measure (Boson 2)))
    (hbound : ∀ t : ℝ, t ≠ 0 → ∀ x : Boson 2, ‖F t x‖ ≤ B x)
    (hint : Integrable B (volume : Measure (Boson 2)))
    (hlim : ∀ x : Boson 2,
      Tendsto (fun t : ℝ => F t x) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    Tendsto
      (fun t : ℝ => ∫ x : Boson 2, F t x ∂(volume : Measure (Boson 2)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hnonzero : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
  have hbound_event :
      ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
        ∀ᵐ x ∂(volume : Measure (Boson 2)), ‖F t x‖ ≤ B x := by
    filter_upwards [hnonzero] with t ht
    exact Filter.Eventually.of_forall (hbound t ht)
  have hintegral :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure (Boson 2))) B
      (Filter.Eventually.of_forall hmeas) hbound_event hint
      (Filter.Eventually.of_forall hlim)
  simpa only [integral_zero] using hintegral

/-- Generic squared-norm error tends to zero when the vector
itself tends to its proposed limit. -/
theorem norm_sub_sq_tendsto_zero_of_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter ℝ} (q : ℝ → E) (v : E)
    (hlim : Tendsto q l (𝓝 v)) :
    Tendsto (fun t : ℝ => ‖q t - v‖ ^ 2) l (𝓝 (0 : ℝ)) := by
  -- #297: an untyped tendsto_const_nhds leaves the subtracted
  -- constant as an unresolved metavariable. Fix the constant v at
  -- the abstract normed-fiber level before taking the squared norm.
  have hconst : Tendsto (fun _ : ℝ => v) l (𝓝 v) :=
    tendsto_const_nhds
  have hsub : Tendsto (fun t : ℝ => q t - v) l (𝓝 (v - v)) :=
    hlim.sub hconst
  have hsq : Tendsto (fun t : ℝ => ‖q t - v‖ ^ 2) l
      (𝓝 (‖v - v‖ ^ 2)) := hsub.norm.pow 2
  simpa only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hsq

#print axioms originalBosonVolume_puncturedDCT_squaredError
#print axioms norm_sub_sq_tendsto_zero_of_tendsto
#check @originalBosonVolume_puncturedDCT_squaredError
#check @norm_sub_sq_tendsto_zero_of_tendsto

end
end FCP.BFSSSU2PhysicalDomainL6H5E6A
