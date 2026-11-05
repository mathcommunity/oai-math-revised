import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D2COriginalExteriorPBWBasisOrderedWordProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D2DOriginalExteriorPBWEmptyAndEraseInjectivityProbe

/-! Owner FCP source-only port, original cc608e2282e1b32bb11bbb64424e4775b28138e2; Git blob 96adf2cf80e5dd81c71220e0cb811cf9b8494cf3.
Imports alone have been restructured; theorem statements/proof bodies unchanged.
The omitted original Spin ancestry is not claimed qualified by this port.
Status: provisional pending fresh owner strict-gate acceptance. -/

/-!
K1D2E4 — literal original-source finite-support occupancy.

For any actual original exterior element x, its coefficients have
finite support in the F20B Finset-indexed basis. Because the original
source has EXACTLY 48 real Majorana coordinate labels, we form the
finite set of coordinates belonging to any occupied basis index.
Its least coordinate under the SAME F20B well-order is no greater
than every source label in any supported basis index.

This prepares the final scalar-common-kernel proof without a
global signed contraction matrix or artificial 2^48 enumeration.
The final scalar theorem is NOT asserted here; this file remains
staged until the strict original Lean/axiom gate accepts it.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52K1D2E4
noncomputable section
open FCP.BFSSS1V0

private abbrev E := ExteriorAlgebra ℝ Source48Vector

local instance : LinearOrder Source48Label := by
  classical
  exact linearOrderOfSTO WellOrderingRel
local instance : LE Source48Label :=
  (instDistribLatticeOfLinearOrder (α := Source48Label)).toSemilatticeInf.toLE

/-- Finite set of original coordinate labels which belong to
some nonzero original F20B exterior PBW basis coefficient. -/
noncomputable def originalSourcePBWOccupiedLabels (x : E) :
    Finset Source48Label := by
  classical
  exact Finset.univ.filter (fun j =>
    ∃ I ∈ (FCP.BFSSS1V52K1D2C.originalSourceExteriorPBWBasis.repr x).support,
      j ∈ I)

/-- Every coordinate of a basis index in the true finitely
supported PBW coefficient expansion belongs to the occupied labels. -/
theorem originalSourcePBWSupportedIndex_member_occupied
    (x : E) (I : Finset Source48Label)
    (hI : I ∈ (FCP.BFSSS1V52K1D2C.originalSourceExteriorPBWBasis.repr x).support)
    (j : Source48Label) (hj : j ∈ I) :
    j ∈ originalSourcePBWOccupiedLabels x := by
  classical
  simp only [originalSourcePBWOccupiedLabels, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨I, hI, hj⟩

/-- The least occupied original 48-real coordinate is bounded
above by every coordinate of every supported original PBW index. -/
theorem originalSourcePBWLeastOccupied_le_every_supported_coordinate
    (x : E) (hocc : (originalSourcePBWOccupiedLabels x).Nonempty)
    (I : Finset Source48Label)
    (hI : I ∈ (FCP.BFSSS1V52K1D2C.originalSourceExteriorPBWBasis.repr x).support)
    (k : Source48Label) (hk : k ∈ I) :
    (originalSourcePBWOccupiedLabels x).min' hocc ≤ k := by
  exact Finset.min'_le _ k
    (originalSourcePBWSupportedIndex_member_occupied x I hI k hk)

#print axioms originalSourcePBWSupportedIndex_member_occupied
#print axioms originalSourcePBWLeastOccupied_le_every_supported_coordinate

end
end FCP.BFSSS1V52K1D2E4
