import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B10B1JointHaarFubiniIntegrabilityProbe

/-!
# BFSS SU2 D2B10B2 — genuine Haar/spatial Fubini against a smooth-core test

PROSPECTIVE / UNCOMPILED until the pinned Lean Actions gate passes.

D2B10B1 proves product-measure integrability of the actual BFSS
fermion-valued SU2 Haar integrand. Here we advance from mere integrability
to a true Fubini interchange, and to its pairing with an original
SmoothCore test section. We use only the original GaugeData and
sourceHaar, original source SmoothCore and spatial volume.

The smooth test is bounded and compactly supported; the weighted
scalar integrand is continuous and compactly supported. Neither
pointwise evaluation of arbitrary Lp equivalence classes, nor a
hypothetical Lp-to-test embedding, is introduced.

The final L2 Bochner/pointwise compatibility and physical norm-core
density equality are NOT claimed in this leaf.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B10B2
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open OAI.Laughlin.Rotation
open FCP.BFSSSU2PhysicalDomainD2B1
open FCP.BFSSSU2PhysicalDomainD2B2
open FCP.BFSSSU2PhysicalDomainD2B10B1
open MeasureTheory Set
open scoped InnerProductSpace

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- The original fermion-valued joint gauge integrand satisfies
actual Haar/spatial Fubini, since D2B10B1 proves genuine
product-measure Bochner integrability, in the correct orientation. -/
theorem sourceHaarFubini_vector (f : SmoothCore 2) :
    (∫ g : GaugeGroup 2,
      ∫ x : Boson 2, G.fermion g (f (G.boson g⁻¹ x))
        ∂(volume : Measure (Boson 2)) ∂sourceHaar) =
      (∫ x : Boson 2,
        ∫ g : GaugeGroup 2, G.fermion g (f (G.boson g⁻¹ x))
          ∂sourceHaar ∂(volume : Measure (Boson 2))) := by
  exact integral_integral_swap (sourceHaarJoint_integrable_swapped M G f)

/-- The weighted gauge/spatial scalar inner product is
integrable over the genuine Haar × volume product measure.

An original SmoothCore test h is smooth and compactly supported,
so the weighted integrand vanishes outside SU2 × tsupport h.
No extra measure hypotheses are introduced. -/
theorem sourceHaarInnerJoint_integrable (f h : SmoothCore 2) :
    Integrable
      (fun p : GaugeGroup 2 × Boson 2 =>
        inner ℂ (h p.2)
          (G.fermion p.1 (f (G.boson p.1⁻¹ p.2))))
      (sourceHaar.prod (volume : Measure (Boson 2))) := by
  have hF : Continuous (fun p : GaugeGroup 2 × Boson 2 =>
      G.fermion p.1 (f (G.boson p.1⁻¹ p.2))) :=
    (sourceHaarIntegrand_jointContinuous M G f).comp continuous_swap
  have hH : Continuous (fun p : GaugeGroup 2 × Boson 2 => h p.2) :=
    h.continuous.comp continuous_snd
  have hcompact :
      HasCompactSupport (fun p : GaugeGroup 2 × Boson 2 =>
        inner ℂ (h p.2)
          (G.fermion p.1 (f (G.boson p.1⁻¹ p.2)))) := by
    have hc : IsCompact ((Set.univ : Set (GaugeGroup 2)) ×ˢ
        tsupport (h : Boson 2 → Fermion 2)) :=
      isCompact_univ.prod h.hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact hc
    intro p hp
    by_contra hn
    have hz : h p.2 = 0 := by
      by_contra hnonzero
      have hs : p.2 ∈ tsupport (h : Boson 2 → Fermion 2) := by
        apply subset_closure
        simpa only [Function.mem_support] using hnonzero
      exact hn ⟨Set.mem_univ _, hs⟩
    exact (Function.mem_support.mp hp) (by simp [hz])
  exact (hH.inner hF).integrable_of_hasCompactSupport hcompact

/-- Fubini for the genuine complex scalar pairing of a test
section with the source SU2 gauge orbit. -/
theorem sourceHaarFubini_inner (f h : SmoothCore 2) :
    (∫ g : GaugeGroup 2,
      ∫ x : Boson 2,
        inner ℂ (h x) (G.fermion g (f (G.boson g⁻¹ x)))
        ∂(volume : Measure (Boson 2)) ∂sourceHaar) =
      (∫ x : Boson 2,
        ∫ g : GaugeGroup 2,
          inner ℂ (h x) (G.fermion g (f (G.boson g⁻¹ x)))
          ∂sourceHaar ∂(volume : Measure (Boson 2))) := by
  exact integral_integral_swap (sourceHaarInnerJoint_integrable M G f h)

/-- The source scalar weighted-Fubini result, explicitly identifying
the inner Haar integral with the original pointwise SmoothCore average.
This will be used to identify Bochner Haar averages by pairing. -/
theorem sourceHaarFubini_inner_eq_raw (f h : SmoothCore 2) :
    (∫ g : GaugeGroup 2,
      ∫ x : Boson 2,
        inner ℂ (h x) (G.fermion g (f (G.boson g⁻¹ x)))
        ∂(volume : Measure (Boson 2)) ∂sourceHaar) =
      (∫ x : Boson 2,
        inner ℂ (h x) (sourceHaarAverageRaw M G f x)
          ∂(volume : Measure (Boson 2))) := by
  rw [sourceHaarFubini_inner M G f h]
  apply integral_congr_ae
  filter_upwards [] with x
  change (∫ g : GaugeGroup 2,
      inner ℂ (h x) (G.fermion g (f (G.boson g⁻¹ x)))
      ∂sourceHaar) =
    inner ℂ (h x)
      (∫ g : GaugeGroup 2,
        G.fermion g (f (G.boson g⁻¹ x)) ∂sourceHaar)
  exact integral_inner (sourceHaarIntegrand_integrable M G f x) (h x)

#print axioms sourceHaarFubini_vector
#print axioms sourceHaarInnerJoint_integrable
#print axioms sourceHaarFubini_inner
#print axioms sourceHaarFubini_inner_eq_raw

end
end FCP.BFSSSU2PhysicalDomainD2B10B2
