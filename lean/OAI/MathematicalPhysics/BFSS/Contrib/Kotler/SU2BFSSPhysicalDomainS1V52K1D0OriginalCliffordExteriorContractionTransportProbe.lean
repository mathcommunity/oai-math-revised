import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1COriginalSpin48CliffordPolarContractionProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52L9E5F20BOriginalSource48CliffordPBWBasisFiniteDimensionalProbe

/-! Owner import from FCP cc608e2282e1b32bb11bbb64424e4775b28138e2,
original source blob c3a96cb1abd32e3cfaa82ed515224bb958e2c4eb.
Only imports and this provenance comment are adapted. Definitions, theorem
statements and proof bodies below are source-exact. Local candidate only
until an independent owner strict gate passes. -/

/-!
K1D0 — first original-source Clifford/exterior contraction bridge.

The pinned Mathlib changeForm_contractLeft theorem transports contraction
through equivExterior (a REAL LINEAR equivalence, NOT an algebra hom).
Composing with strictly accepted K1C shows every source vector-action
kernel element maps into the common kernel of original polar contractions
on the actual exterior algebra of the original 48-real source labels.

This does NOT prove common contraction kernel = scalar, nor full Spin48
two-sign kernel, covering, global Spin9, or physical spectral claims.
Staged pending pinned strict Lean/axiom certification.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52K1D0
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev E := ExteriorAlgebra ℝ Source48Vector

/-- Native contraction commutes with the actual source Clifford/
exterior REAL-linear change of form, with no multiplicativity assumption. -/
theorem originalSourceClifford_exterior_contractLeft_transport
    (d : Module.Dual ℝ Source48Vector) (x : C) :
    (CliffordAlgebra.equivExterior Q) (CliffordAlgebra.contractLeft d x) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ Source48Vector))
        d ((CliffordAlgebra.equivExterior Q) x) := by
  simpa only [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply]
    using (CliffordAlgebra.changeForm_contractLeft
      (h := CliffordAlgebra.changeForm.associated_neg_proof)
      d x)

/-- A genuine source Spin48 element acting trivially on the original
48-real vectors has all original polar contractions zero after
transport into the exact exterior algebra. This is a reduction, not
the still-open coefficient separation. -/
theorem originalSourceSpin48_trivialAction_exteriorPolarContractions_zero
    (s : spinGroup Q)
    (hs : ∀ v : Source48Vector,
      FCP.BFSSS1V31.sourceSpin48VectorAction s v = v) :
    ∀ v : Source48Vector,
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ Source48Vector))
        (Q.polarBilin v) ((CliffordAlgebra.equivExterior Q) (s : C)) = 0 := by
  intro v
  rw [← originalSourceClifford_exterior_contractLeft_transport]
  rw [FCP.BFSSS1V52K1C.originalSourceSpin48_trivialAction_polarContractions_zero s hs v]
  exact map_zero (CliffordAlgebra.equivExterior Q)

#print axioms originalSourceClifford_exterior_contractLeft_transport
#print axioms originalSourceSpin48_trivialAction_exteriorPolarContractions_zero

end
end FCP.BFSSS1V52K1D0
