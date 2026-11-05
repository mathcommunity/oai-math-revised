import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D2AOriginalExteriorCoordinateWordContractionProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52L9E5F20BOriginalSource48CliffordPBWBasisFiniteDimensionalProbe
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-! Owner FCP source-only port, original cc608e2282e1b32bb11bbb64424e4775b28138e2; Git blob b494be954703d29b9d70ad934546bebf9a55cbcf.
Imports alone have been restructured; theorem statements/proof bodies unchanged.
The omitted original Spin ancestry is not claimed qualified by this port.
Status: provisional pending fresh owner strict-gate acceptance. -/

/-!
K1D2D — independently prove the empty source-exterior PBW basis
monomial is the scalar unit, and that finite-subset erasure at a
known present ORIGINAL source coordinate is injective.

This is an independent input to the eventual exterior-coefficient
separation, not a full scalar-common-kernel or Clifford center proof.
The same exact F20B source well-order is used, not a guessed
color-major ordering, and no exterior-algebra multiplication is
transported through `equivExterior`.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52K1D2D
noncomputable section
open FCP.BFSSS1V0

private abbrev E := ExteriorAlgebra ℝ Source48Vector
local instance : LinearOrder Source48Label := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- The empty index of the ACTUAL F20B exterior basis represents
the multiplicative unit, which is the real scalar 1. -/
theorem originalSourceExteriorPBWBasis_empty_eq_one :
    (Pi.basisFun ℝ Source48Label).ExteriorAlgebra
      (∅ : Finset Source48Label) = (1 : E) := by
  classical
  simp only [ExteriorAlgebra.basis_apply, Finset.card_empty,
    ExteriorAlgebra.ιMulti_family]
  exact ExteriorAlgebra.ιMulti_zero_apply (R := ℝ) _

/-- Erasure is injective on finite subsets which contain the
same literal source coordinate j. No global enumeration is needed. -/
theorem originalSourceFinset_erase_injective_at_present_label
    (j : Source48Label) (I J : Finset Source48Label)
    (hI : j ∈ I) (hJ : j ∈ J)
    (h : I.erase j = J.erase j) : I = J := by
  calc
    I = insert j (I.erase j) := (Finset.insert_erase hI).symm
    _ = insert j (J.erase j) := by rw [h]
    _ = J := Finset.insert_erase hJ

#print axioms originalSourceExteriorPBWBasis_empty_eq_one
#print axioms originalSourceFinset_erase_injective_at_present_label

end
end FCP.BFSSS1V52K1D2D
