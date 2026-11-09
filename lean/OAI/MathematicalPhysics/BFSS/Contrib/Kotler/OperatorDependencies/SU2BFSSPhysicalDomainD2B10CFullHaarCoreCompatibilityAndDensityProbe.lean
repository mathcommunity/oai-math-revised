import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B10B2SmoothTestInnerFubiniProbe

/-!
# BFSS SU2 D2B10C — genuine original Haar L²/core compatibility and physical density

PROSPECTIVE / UNCOMPILED until exact pinned GitHub Lean gate succeeds.

D2B10B2 has formally justified the Fubini interchange for the
complex scalar pairing of the original pointwise SU2 gauge integrand
against EVERY original SmoothCore test function.

This leaf uses the ACTUAL L2 inner product, the accepted D2B7
gauge-action/core almost-everywhere identification, the exact
D2B9A Bochner integrability, and the B10B2 source Fubini theorem
to identify the two Haar averages by their pairings with all
source smooth tests. The accepted original coreToL2_dense theorem
then proves equality of the two full-Hilbert vectors.

This supplies the formerly open D2B10A compatibility hypothesis
unconditionally, yielding the exact source physical-space density:
  G.coreNormClosure = G.physicalSpace.

No surrogate representation, unbounded L2 point evaluation,
unproved physics assumption, or admitted axiom is used.
Both statements remain PROSPECTIVE until compiler and axiom PASS.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B10C
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open OAI.Laughlin.Rotation
open FCP.BFSSSU2PhysicalDomainD2B1
open FCP.BFSSSU2PhysicalDomainD2B4
open FCP.BFSSSU2PhysicalDomainD2B6
open FCP.BFSSSU2PhysicalDomainD2B7
open FCP.BFSSSU2PhysicalDomainD2B9A
open FCP.BFSSSU2PhysicalDomainD2B9B
open FCP.BFSSSU2PhysicalDomainD2B10A
open FCP.BFSSSU2PhysicalDomainD2B10B2
open MeasureTheory Set
open scoped InnerProductSpace

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- The true full-L2 SU2 Bochner Haar average and the
original pointwise SmoothCore Haar average have IDENTICAL complex
Hilbert inner products against every original smooth test section.

The Hilbert Bochner integral is moved only through the bounded
inner-product functional, never through point evaluation on L2. -/
theorem sourceFullHaarAverageCLM_testInner_eq
    (f h : SmoothCore 2) :
    inner ℂ (coreToL2 h)
      (sourceFullHaarAverageCLM M G (coreToL2 f)) =
    inner ℂ (coreToL2 h)
      (coreToL2 (sourceHaarAverageCore M G f)) := by
  rw [sourceFullHaarAverageCLM_apply]
  unfold sourceFullHaarAverage
  calc
    _ = ∫ g : GaugeGroup 2,
        inner ℂ (coreToL2 h)
          (sourceFullGaugePairCLM M G g (coreToL2 f)) ∂sourceHaar := by
        exact (integral_inner
          (sourceFullHaarIntegrand_integrable M G (coreToL2 f))
          (coreToL2 h)).symm
    _ = ∫ g : GaugeGroup 2,
        ∫ x : Boson 2,
          inner ℂ (h x)
            (G.fermion g (f (G.boson g⁻¹ x)))
          ∂(volume : Measure (Boson 2)) ∂sourceHaar := by
        apply integral_congr_ae
        filter_upwards [] with g
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [coreToL2_ae h,
          sourceFullGaugePairCLM_core_ae M G f g] with x hh hf
        rw [hh, hf]
    _ = ∫ x : Boson 2,
        inner ℂ (h x)
          (sourceHaarAverageRaw M G f x)
        ∂(volume : Measure (Boson 2)) :=
      sourceHaarFubini_inner_eq_raw M G f h
    _ = inner ℂ (coreToL2 h)
          (coreToL2 (sourceHaarAverageCore M G f)) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [coreToL2_ae h,
          coreToL2_ae (sourceHaarAverageCore M G f)] with x hh ha
        rw [hh, ha]
        rfl

/-- UNCONDITIONAL equality of original full-Hilbert Haar Bochner
averaging and the embedded genuine source smooth-core Haar average.
D2B10B2 establishes the pairings; the original accepted
coreToL2_dense identifies the full-Hilbert vectors. -/
theorem sourceFullHaarAverageCLM_coreToL2_compat
    (f : SmoothCore 2) :
    sourceFullHaarAverageCLM M G (coreToL2 f) =
      coreToL2 (sourceHaarAverageCore M G f) := by
  let v : FullL2 2 := sourceFullHaarAverageCLM M G (coreToL2 f)
  let w : FullL2 2 := coreToL2 (sourceHaarAverageCore M G f)
  change v = w
  have heq (h : SmoothCore 2) :
      inner ℂ (coreToL2 h) v = inner ℂ (coreToL2 h) w :=
    sourceFullHaarAverageCLM_testInner_eq M G f h
  have horth (h : SmoothCore 2) :
      inner ℂ (coreToL2 h) (v - w) = 0 := by
    simpa only [inner_sub_right, sub_eq_zero] using heq h
  have hcont : Continuous (fun u : FullL2 2 => inner ℂ u (v - w)) :=
    continuous_id.inner continuous_const
  have hclosed :
      IsClosed {u : FullL2 2 | inner ℂ u (v - w) = 0} :=
    isClosed_singleton.preimage hcont
  have hrange :
      Set.range (coreToL2 (N := 2)) ⊆
        {u : FullL2 2 | inner ℂ u (v - w) = 0} := by
    rintro u ⟨h, rfl⟩
    exact horth h
  have hcl : v - w ∈ closure (Set.range (coreToL2 (N := 2))) := by
    rw [(coreToL2_dense (N := 2)).closure_range]
    trivial
  have hz : inner ℂ (v - w) (v - w) = 0 :=
    (closure_minimal hrange hclosed) hcl
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

/-- FINAL exact BFSS SU2 physical density statement for the
original source GaugeData: the L2-closure of its original gauge-
invariant smooth core equals its original physical Hilbert subspace.

This is a source-defined Hilbert-space density theorem, NOT
a theorem about Hamiltonian spectra, supersymmetric vacua,
mass gaps, or empirical BFSS validity. -/
theorem sourceCoreNormClosure_eq_physical_unconditional :
    G.coreNormClosure = G.physicalSpace :=
  sourceCoreNormClosure_eq_physical_of_Haar_core_compat M G
    (sourceFullHaarAverageCLM_coreToL2_compat M G)

#print axioms sourceFullHaarAverageCLM_testInner_eq
#print axioms sourceFullHaarAverageCLM_coreToL2_compat
#print axioms sourceCoreNormClosure_eq_physical_unconditional

end
end FCP.BFSSSU2PhysicalDomainD2B10C
