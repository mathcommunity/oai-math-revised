import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D2COriginalExteriorPBWBasisOrderedWordProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D2DOriginalExteriorPBWEmptyAndEraseInjectivityProbe
import Mathlib.Data.Finset.Sort

/-! Owner FCP source-only port, original cc608e2282e1b32bb11bbb64424e4775b28138e2; Git blob ed3b405c1a1f7b33e44199ad5a635c3926d6b721.
Imports alone have been restructured; theorem statements/proof bodies unchanged.
The omitted original Spin ancestry is not claimed qualified by this port.
Status: provisional pending fresh owner strict-gate acceptance. -/

/-!
K1D2E2 — the exact original F20B well-ordered PBW coordinate list
is the canonical orderEmbOfFin sorted Finset list. A least member of
a genuine Finset index then is the leading label, with remaining list
the corresponding Finset.erase j.

This source lemma removes the requirement for a full signed
contraction-matrix expansion in the eventual scalar-common-kernel
proof: choose the least occupied original source label across the
finite support of an arbitrary exterior basis expansion.

No surrogates for Source48Label or F20B's noncomputable well-order,
no new axioms, and no scalar-kernel claim in this module.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52K1D2E2
noncomputable section
open FCP.BFSSS1V0

local instance : LinearOrder Source48Label := by
  classical
  exact linearOrderOfSTO WellOrderingRel

-- The product label type also has a pre-existing product order. Force
-- its LE to be the SAME noncomputable F20B well-order as above.
local instance : LE Source48Label :=
  (instDistribLatticeOfLinearOrder (α := Source48Label)).toSemilatticeInf.toLE

/-- The frozen original PBW ordered label list is literally the
canonical sorted Finset under the SAME original source well-order. -/
theorem originalSourcePBWOrderedLabels_eq_finsetSort
    (I : Finset Source48Label) :
    FCP.BFSSS1V52K1D2C.originalSourceExteriorPBWOrderedLabels I =
      I.sort := by
  classical
  change (List.ofFn (fun i : Fin I.card => I.orderEmbOfFin rfl i)) = I.sort
  rw [List.ofFn_eq_map]
  exact Finset.listMap_orderEmbOfFin_finRange I rfl

/-- If j is the least coordinate in the original finite PBW index,
it occurs first, and the remaining ordered word is EXACTLY the
original ordered word of I.erase j. -/
theorem originalSourcePBWOrderedLabels_cons_of_least
    (I : Finset Source48Label) (j : Source48Label)
    (hj : j ∈ I) (hmin : ∀ k ∈ I, j ≤ k) :
    FCP.BFSSS1V52K1D2C.originalSourceExteriorPBWOrderedLabels I =
      j :: FCP.BFSSS1V52K1D2C.originalSourceExteriorPBWOrderedLabels (I.erase j) := by
  classical
  rw [originalSourcePBWOrderedLabels_eq_finsetSort,
    originalSourcePBWOrderedLabels_eq_finsetSort]
  have hmin' : ∀ k ∈ I.erase j, j ≤ k := by
    intro k hk
    exact hmin k (Finset.mem_of_mem_erase hk)
  calc
    I.sort = (insert j (I.erase j)).sort := by rw [Finset.insert_erase hj]
    _ = j :: (I.erase j).sort := by
      exact Finset.sort_insert (r := LE.le) hmin' (by simp)

#print axioms originalSourcePBWOrderedLabels_eq_finsetSort
#print axioms originalSourcePBWOrderedLabels_cons_of_least

end
end FCP.BFSSS1V52K1D2E2
