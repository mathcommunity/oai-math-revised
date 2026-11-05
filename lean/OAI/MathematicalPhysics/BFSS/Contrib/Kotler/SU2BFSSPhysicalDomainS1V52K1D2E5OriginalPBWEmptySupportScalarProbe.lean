import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D2E4OriginalPBWFinitelyOccupiedMinimumProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D2DOriginalExteriorPBWEmptyAndEraseInjectivityProbe

/-! Owner FCP source-only port, original cc608e2282e1b32bb11bbb64424e4775b28138e2; Git blob 50943cf5f20a40cb8f65b1e90d6ca738af3bc660.
Imports have been restructured; the theorem statement is unchanged.
The original staged E5 proof is repaired for the pinned Mathlib interface:
empty membership by simp, and repr reconstruction by congrArg.
The omitted original Spin ancestry is not claimed qualified by this port.
Status: provisional pending fresh owner strict-gate acceptance. -/

/-!
K1D2E5 — reconstruct the exact original exterior scalar line
from a PBW coordinate expansion having no occupied nonempty index.

This does NOT prove yet that every common coordinate-contraction
kernel element has no occupied labels. That substantive coefficient
elimination is the distinct remaining K1D2E6 obligation.

No assumption of Clifford/exterior multiplicativity, guessed label
ordering, physical Spin9 covariance or spectral existence.
Staged for strict original Lean qualification after E4.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52K1D2E5
noncomputable section
open FCP.BFSSS1V0

private abbrev E := ExteriorAlgebra ℝ Source48Vector
private abbrev B :=
  FCP.BFSSS1V52K1D2C.originalSourceExteriorPBWBasis

local instance : LinearOrder Source48Label := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- When no original source coordinate occurs in a nonzero
finite PBW coefficient, the actual exterior element is scalar.
The scalar is its coefficient at the empty Finset index. -/
theorem originalExteriorScalar_of_no_occupiedPBWLabels
    (x : E)
    (hempty : FCP.BFSSS1V52K1D2E4.originalSourcePBWOccupiedLabels x = ∅) :
    ∃ c : ℝ, x = algebraMap ℝ E c := by
  classical
  let f : Finset Source48Label →₀ ℝ := B.repr x
  have hf : f = Finsupp.single (∅ : Finset Source48Label) (f ∅) := by
    ext I
    by_cases hI : I = ∅
    · subst I
      simp
    · have hc : f I = 0 := by
        by_contra hn
        have hs : I ∈ (B.repr x).support := by
          exact Finsupp.mem_support_iff.mpr (show (B.repr x) I ≠ 0 from hn)
        have hne : I.Nonempty := Finset.nonempty_iff_ne_empty.mpr hI
        obtain ⟨j, hj⟩ := hne
        have hh :=
          FCP.BFSSS1V52K1D2E4.originalSourcePBWSupportedIndex_member_occupied
            x I hs j hj
        rw [hempty] at hh
        simp at hh
      simp [hI, hc]
  refine ⟨f ∅, ?_⟩
  calc
    x = B.repr.symm f := by
      simp [f]
    _ = B.repr.symm (Finsupp.single ∅ (f ∅)) := congrArg B.repr.symm hf
    _ = f ∅ • B (∅ : Finset Source48Label) := B.repr_symm_single ∅ (f ∅)
    _ = algebraMap ℝ E (f ∅) := by
      have hunit : B (∅ : Finset Source48Label) = (1 : E) := by
        simpa [B, FCP.BFSSS1V52K1D2C.originalSourceExteriorPBWBasis] using
          FCP.BFSSS1V52K1D2D.originalSourceExteriorPBWBasis_empty_eq_one
      rw [hunit]
      simp [Algebra.smul_def]

#print axioms originalExteriorScalar_of_no_occupiedPBWLabels

end
end FCP.BFSSS1V52K1D2E5
