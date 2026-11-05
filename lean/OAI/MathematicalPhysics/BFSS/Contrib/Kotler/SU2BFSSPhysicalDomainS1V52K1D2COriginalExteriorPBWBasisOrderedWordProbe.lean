import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D2AOriginalExteriorCoordinateWordContractionProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52L9E5F20BOriginalSource48CliffordPBWBasisFiniteDimensionalProbe
import Mathlib.Data.Finset.Sort

/-! Owner FCP source-only port, original cc608e2282e1b32bb11bbb64424e4775b28138e2; Git blob 99ab3f78e12a31c365f83c1577db852327d3bc3a.
Imports alone have been restructured; theorem statements/proof bodies unchanged.
The omitted original Spin ancestry is not claimed qualified by this port.
Status: provisional pending fresh owner strict-gate acceptance. -/

/-!
K1D2C — identify the exact accepted ORIGINAL F20B exterior basis
with a finite ordered word of literal source Majorana coordinate labels.

The chosen order is the SAME noncomputable
  linearOrderOfSTO WellOrderingRel
used in the accepted original F20B Clifford PBW basis, not a guessed
color-major lexicographic order or a new spinor flattening.

This theorem is the missing bridge from accepted K1D2A exterior
coordinate-word derivative lemmas to F20B's indexed Finset basis.
It does NOT yet prove full coefficient isolation or scalar kernel.
STAGED pending strict original Lean proof/axiom gate.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52K1D2C
noncomputable section
open FCP.BFSSS1V0
open FCP.BFSSS1V52K1D2A

private abbrev E := ExteriorAlgebra ℝ Source48Vector

-- File-local exact ordering, identical to F20B's private `letI`.
local instance : LinearOrder Source48Label := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- The EXACT exterior basis on the original 48-label space used
before the genuine F20B Clifford/exterior real-linear equivalence. -/
noncomputable def originalSourceExteriorPBWBasis :
    Module.Basis (Finset Source48Label) ℝ E :=
  (Pi.basisFun ℝ Source48Label).ExteriorAlgebra

/-- Finite labels sorted using the exact original F20B local well-order. -/
noncomputable def originalSourceExteriorPBWOrderedLabels
    (I : Finset Source48Label) : List Source48Label :=
  List.ofFn (fun i : Fin I.card => I.orderEmbOfFin rfl i)

/-- Exact F20B exterior PBW monomial equals its ordered original
source Majorana coordinate exterior word. -/
theorem originalSourceExteriorPBWBasis_eq_originalCoordinateWord
    (I : Finset Source48Label) :
    originalSourceExteriorPBWBasis I =
      originalExteriorCoordinateWord (originalSourceExteriorPBWOrderedLabels I) := by
  classical
  change (Pi.basisFun ℝ Source48Label).ExteriorAlgebra I =
    originalExteriorCoordinateWord
      (List.ofFn (fun i : Fin I.card => I.orderEmbOfFin rfl i))
  rw [ExteriorAlgebra.basis_apply]
  unfold ExteriorAlgebra.ιMulti_family
  rw [ExteriorAlgebra.ιMulti_apply]
  simp only [originalExteriorCoordinateWord,
    Set.powersetCard.prodEquiv_symm_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply,
    List.ofFn_eq_map, List.map_map, Function.comp_apply,
    Pi.basisFun_apply]
  rfl

/-- Ordered original PBW basis label words have no repetitions. -/
theorem originalSourceExteriorPBWOrderedLabels_nodup
    (I : Finset Source48Label) :
    (originalSourceExteriorPBWOrderedLabels I).Nodup := by
  classical
  change (List.ofFn (fun i : Fin I.card =>
    I.orderEmbOfFin rfl i)).Nodup
  exact List.nodup_ofFn.mpr (I.orderEmbOfFin rfl).injective

#print axioms originalSourceExteriorPBWBasis_eq_originalCoordinateWord
#print axioms originalSourceExteriorPBWOrderedLabels_nodup

end
end FCP.BFSSS1V52K1D2C
