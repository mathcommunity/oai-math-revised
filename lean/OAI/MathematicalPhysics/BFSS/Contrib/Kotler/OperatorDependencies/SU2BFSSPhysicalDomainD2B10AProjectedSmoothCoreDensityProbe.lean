import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B9CGenuineGaugeHaarProjectionProbe

/-!
# BFSS SU2 D2B10A — projected original smooth-core density in physical L2

PROSPECTIVE / UNCOMPILED until exact pinned CI acceptance.

D2B9C proves that the genuine original SU2 Haar projection P is a
bounded linear operator with range exactly GaugeData.physicalSpace,
and fixes every original physical Hilbert vector.

Combined with the original coreToL2_dense theorem, this implies:
  closure { P(coreToL2 f) | f : SmoothCore 2 } = G.physicalSpace.
This is unconditional mathematical progress on the exact source objects.

The subsequent result is EXPLICITLY CONDITIONAL on the still-open
full-Hilbert / smooth-test Haar compatibility identity, and gives
the exact remaining bridge to coreNormClosure = physicalSpace.

The condition is NOT claimed to have been discharged.
No external physics assumption, surrogate core, or axiom is introduced.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B10A
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2A
open FCP.BFSSSU2PhysicalDomainD2B4
open FCP.BFSSSU2PhysicalDomainD2B9B
open FCP.BFSSSU2PhysicalDomainD2B9C
open MeasureTheory Set

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- The original BFSS SmoothCore vectors, AFTER the genuine
bounded source full-Hilbert Haar projection, have dense range
in the exact source-defined physicalSpace.

This theorem does NOT yet assert that these projected vectors
are themselves images of original invariant SmoothCore functions. -/
theorem sourceProjectedSmoothCore_closure_eq_physical :
    closure (Set.range (fun f : SmoothCore 2 =>
      sourceFullHaarAverageCLM M G (coreToL2 f))) =
        (G.physicalSpace : Set (FullL2 2)) := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro v ⟨f, rfl⟩
      exact sourceFullHaarAverageCLM_mem_physical M G (coreToL2 f)
    · exact G.physicalSpace_closed
  · intro v hv
    have hcl : v ∈ closure (Set.range (coreToL2 (N := 2))) := by
      rw [(coreToL2_dense (N := 2)).closure_range]
      trivial
    have himage : v ∈
        (sourceFullHaarAverageCLM M G) ''
          closure (Set.range (coreToL2 (N := 2))) :=
      ⟨v, hcl, sourceFullHaarAverageCLM_fixed_physical M G v hv⟩
    have h := (image_closure_subset_closure_image
      (s := Set.range (coreToL2 (N := 2)))
      (sourceFullHaarAverageCLM M G).continuous) himage
    have heq :
        (sourceFullHaarAverageCLM M G) ''
          Set.range (coreToL2 (N := 2)) =
        Set.range (fun f : SmoothCore 2 =>
          sourceFullHaarAverageCLM M G (coreToL2 f)) := by
      ext w
      constructor
      · rintro ⟨u, ⟨f, rfl⟩, rfl⟩
        exact ⟨f, rfl⟩
      · rintro ⟨f, rfl⟩
        exact ⟨coreToL2 f, ⟨f, rfl⟩, rfl⟩
    rw [heq] at h
    exact h

/-- The exact final density equality follows if and ONLY IF WE
DISCHARGE the stated source projection/core-averaging compatibility.

This is a CONDITIONAL reduction, not an unconditional density proof.
D2B10B must prove the displayed hcompat from original integrations. -/
theorem sourceCoreNormClosure_eq_physical_of_Haar_core_compat
    (hcompat : ∀ f : SmoothCore 2,
      sourceFullHaarAverageCLM M G (coreToL2 f) =
        coreToL2 (sourceHaarAverageCore M G f)) :
    G.coreNormClosure = G.physicalSpace := by
  apply le_antisymm
  · exact sourceCoreNormClosure_le_physicalSpace M G
  · intro v hv
    have hcl : v ∈ closure (Set.range (fun f : SmoothCore 2 =>
        sourceFullHaarAverageCLM M G (coreToL2 f))) := by
      rw [sourceProjectedSmoothCore_closure_eq_physical M G]
      exact hv
    have hsubset : Set.range (fun f : SmoothCore 2 =>
        sourceFullHaarAverageCLM M G (coreToL2 f)) ⊆
          (G.coreNormClosure : Set (FullL2 2)) := by
      rintro w ⟨f, rfl⟩
      change sourceFullHaarAverageCLM M G (coreToL2 f) ∈ G.coreNormClosure
      rw [hcompat f]
      have hm : coreToL2 (sourceHaarAverageCore M G f) ∈
          LinearMap.range (coreToL2.comp G.invariantCore.subtype) := by
        exact ⟨⟨sourceHaarAverageCore M G f,
          sourceHaarAverageCore_mem_invariantCore M G f⟩, rfl⟩
      change coreToL2 (sourceHaarAverageCore M G f) ∈
        (LinearMap.range (coreToL2.comp G.invariantCore.subtype)).topologicalClosure
      exact Submodule.le_topologicalClosure _ hm
    have hclosed : IsClosed (G.coreNormClosure : Set (FullL2 2)) := by
      change IsClosed ((LinearMap.range
        (coreToL2.comp G.invariantCore.subtype)).topologicalClosure : Set (FullL2 2))
      exact Submodule.isClosed_topologicalClosure _
    exact (closure_minimal hsubset hclosed) hcl

#print axioms sourceProjectedSmoothCore_closure_eq_physical
#print axioms sourceCoreNormClosure_eq_physical_of_Haar_core_compat

end
end FCP.BFSSSU2PhysicalDomainD2B10A
