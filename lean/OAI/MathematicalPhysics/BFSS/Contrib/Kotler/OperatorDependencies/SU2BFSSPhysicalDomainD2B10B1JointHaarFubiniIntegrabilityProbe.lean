import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B10AProjectedSmoothCoreDensityProbe

/-!
# BFSS SU2 D2B10B1 — genuine joint Haar-spatial Bochner integrability

PROSPECTIVE / UNCOMPILED until exact pinned CI gate passes.

The open final theorem equates the original FullL2 Bochner Haar
projection of coreToL2 f with the L2 representative of the original
pointwise Haar-average SmoothCore function.

This leaf proves an intermediate analytic prerequisite: the ORIGINAL
fermion-valued integrand is jointly integrable on the genuine
bosonic-volume × SU2-source-Haar product measure, and also in
the opposite order. The proof derives compact support from the actual
bosonic gauge action's compact orbit of source test-function support;
no Fubini interchange, Lp pointwise evaluation, or density equality
is claimed here.

Only the exact source gauge representation and Haar measure are used.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B10B1
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open OAI.Laughlin.Rotation
open FCP.BFSSSU2PhysicalDomainD2B2
open MeasureTheory Set

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- Source-defined compact saturation of the original smooth
test function's support under the actual source SU2 boson action. -/
private def sourceSpatialSaturation (f : SmoothCore 2) : Set (Boson 2) :=
  (fun p : GaugeGroup 2 × Boson 2 => G.boson p.1 p.2) ''
    (Set.univ ×ˢ tsupport (f : Boson 2 → Fermion 2))

private theorem sourceSpatialSaturation_compact (f : SmoothCore 2) :
    IsCompact (sourceSpatialSaturation M G f) := by
  exact (isCompact_univ.prod f.hasCompactSupport).image G.boson_continuous

/-- The true source joint Haar integrand is compactly supported in
position × group, with no ad-hoc cutoff, due to compact SU2
saturation of the actual smooth-core compact support. -/
theorem sourceHaarJoint_hasCompactSupport (f : SmoothCore 2) :
    HasCompactSupport
      (fun p : Boson 2 × GaugeGroup 2 =>
        G.fermion p.2 (f (G.boson p.2⁻¹ p.1))) := by
  let S := sourceSpatialSaturation M G f
  have hc : IsCompact (S ×ˢ (Set.univ : Set (GaugeGroup 2))) :=
    (sourceSpatialSaturation_compact M G f).prod isCompact_univ
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro p hp
  by_contra hn
  have hinv : G.boson p.2⁻¹ p.1 = (G.boson p.2).symm p.1 := by
    apply (G.boson p.2).injective
    simp
  have hx : f (G.boson p.2⁻¹ p.1) ≠ 0 := by
    intro hz
    apply (Function.mem_support.mp hp)
    have hz' : f ((G.boson p.2).symm p.1) = 0 := by
      rw [← hinv]
      exact hz
    simp [hz']
  have hs : G.boson p.2⁻¹ p.1 ∈ tsupport (f : Boson 2 → Fermion 2) := by
    apply subset_closure
    simpa only [Function.mem_support] using hx
  have hmem : (p.2, G.boson p.2⁻¹ p.1) ∈
      (Set.univ : Set (GaugeGroup 2)) ×ˢ
      tsupport (f : Boson 2 → Fermion 2) := ⟨Set.mem_univ _, hs⟩
  have himage : G.boson p.2 (G.boson p.2⁻¹ p.1) ∈ S :=
    Set.mem_image_of_mem _ hmem
  have hcancel : G.boson p.2 (G.boson p.2⁻¹ p.1) = p.1 := by simp
  exact hn ⟨hcancel ▸ himage, Set.mem_univ _⟩

/-- Fubini-ready source joint integrability in spatial × gauge
measure ordering, with the actual source fermion-valued functions. -/
theorem sourceHaarJoint_integrable (f : SmoothCore 2) :
    Integrable
      (fun p : Boson 2 × GaugeGroup 2 =>
        G.fermion p.2 (f (G.boson p.2⁻¹ p.1)))
      ((volume : Measure (Boson 2)).prod sourceHaar) := by
  exact (sourceHaarIntegrand_jointContinuous M G f).integrable_of_hasCompactSupport
    (sourceHaarJoint_hasCompactSupport M G f)

/-- The same original source integrand is also integrable for the
opposite product-measure order: Haar × spatial volume. -/
theorem sourceHaarJoint_integrable_swapped (f : SmoothCore 2) :
    Integrable
      (fun p : GaugeGroup 2 × Boson 2 =>
        G.fermion p.1 (f (G.boson p.1⁻¹ p.2)))
      (sourceHaar.prod (volume : Measure (Boson 2))) := by
  have hc : Continuous (fun p : GaugeGroup 2 × Boson 2 =>
      G.fermion p.1 (f (G.boson p.1⁻¹ p.2))) :=
    (sourceHaarIntegrand_jointContinuous M G f).comp continuous_swap
  have hs : HasCompactSupport (fun p : GaugeGroup 2 × Boson 2 =>
      G.fermion p.1 (f (G.boson p.1⁻¹ p.2))) :=
    (sourceHaarJoint_hasCompactSupport M G f).comp_homeomorph
      (Homeomorph.prodComm (GaugeGroup 2) (Boson 2))
  exact hc.integrable_of_hasCompactSupport hs

#print axioms sourceHaarJoint_hasCompactSupport
#print axioms sourceHaarJoint_integrable
#print axioms sourceHaarJoint_integrable_swapped

end
end FCP.BFSSSU2PhysicalDomainD2B10B1
