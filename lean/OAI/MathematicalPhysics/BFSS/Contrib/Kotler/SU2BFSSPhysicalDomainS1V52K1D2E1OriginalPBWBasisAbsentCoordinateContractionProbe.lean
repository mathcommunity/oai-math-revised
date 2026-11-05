import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D2COriginalExteriorPBWBasisOrderedWordProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D2DOriginalExteriorPBWEmptyAndEraseInjectivityProbe

/-! Owner FCP source-only port, original cc608e2282e1b32bb11bbb64424e4775b28138e2; Git blob 52b5ce32275839dc2bde947e29ad2e03ed108bb2.
Imports alone have been restructured; theorem statements/proof bodies unchanged.
The omitted original Spin ancestry is not claimed qualified by this port.
Status: provisional pending fresh owner strict-gate acceptance. -/

/-!
K1D2E1 — direct bridge from the STRICTLY ACCEPTED genuine original
F20B exterior finite-subset PBW basis to source coordinate contraction.

The first lemma proves that every element in the exact well-ordered
source enumeration belongs to its index Finset. Thus an exterior PBW
basis word indexed by I is killed by contracting along j not in I,
using accepted K1D2A contraction and K1D2C word identification.

This is a strictly bounded source-exact mathematical precursor, not
a scalar-common-kernel or full Spin48 kernel theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52K1D2E1
noncomputable section
open FCP.BFSSS1V0
open FCP.BFSSS1V52K1D2A

private abbrev E := ExteriorAlgebra ℝ Source48Vector
private abbrev Q0 : QuadraticForm ℝ Source48Vector := 0

local instance : LinearOrder Source48Label := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- Every label listed by the exact original F20B ordered PBW
enumeration is genuinely a member of its original Finset index. -/
theorem originalSourcePBWOrderedLabels_mem_finset
    (I : Finset Source48Label) (j : Source48Label)
    (hj : j ∈ FCP.BFSSS1V52K1D2C.originalSourceExteriorPBWOrderedLabels I) :
    j ∈ I := by
  classical
  change j ∈ List.ofFn (fun i : Fin I.card => I.orderEmbOfFin rfl i) at hj
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hj
  rw [← hi]
  exact Finset.orderEmbOfFin_mem I rfl i

/-- The actual original finite-subset PBW basis monomial has zero
exterior contraction by any source coordinate absent from its index. -/
theorem originalSourceExteriorPBWBasis_coordinateContraction_zero_of_not_mem
    (I : Finset Source48Label) (j : Source48Label) (hj : j ∉ I) :
    CliffordAlgebra.contractLeft (Q := Q0)
      (LinearMap.proj j : Module.Dual ℝ Source48Vector)
      (FCP.BFSSS1V52K1D2C.originalSourceExteriorPBWBasis I) = 0 := by
  rw [FCP.BFSSS1V52K1D2C.originalSourceExteriorPBWBasis_eq_originalCoordinateWord]
  apply originalExteriorCoordinateWord_contraction_zero_of_not_mem
  intro h
  exact hj (originalSourcePBWOrderedLabels_mem_finset I j h)

#print axioms originalSourcePBWOrderedLabels_mem_finset
#print axioms originalSourceExteriorPBWBasis_coordinateContraction_zero_of_not_mem

end
end FCP.BFSSS1V52K1D2E1
