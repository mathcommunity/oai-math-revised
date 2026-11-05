import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D5OriginalCliffordScalarTransportProbe

/-!
K1D6 — original source Spin(48) kernel scalar star and norm consequences.

Uses qualified K1D5 scalar Clifford result plus the actual pinned
Mathlib CliffordAlgebra.star_algebraMap and spinGroup.star_mul_self_of_mem
theorems, without a guessed spinor representation or algebra equivalence.

This only establishes star-fixedness and square-one INSIDE the original
Clifford algebra. It does not yet establish the real scalar coefficient
equals +1 or -1, prove negative-sign membership, or classify a covering.
CANDIDATE pending independent strict owner verification.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52K1D6
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Trivial action forces the genuine source Spin(48) element to be
Clifford-star fixed because K1D5 has made it a real scalar. -/
theorem originalSourceSpin48_trivialAction_clifford_star_fixed
    (s : spinGroup Q)
    (hs : ∀ v : Source48Vector,
      FCP.BFSSS1V31.sourceSpin48VectorAction s v = v) :
    star (s : C) = (s : C) := by
  obtain ⟨c, hc⟩ :=
    FCP.BFSSS1V52K1D5.originalSourceSpin48_trivialAction_clifford_scalar s hs
  rw [hc, CliffordAlgebra.star_algebraMap]

/-- In the ORIGINAL Clifford algebra, trivial-action Spin elements
square to one by the genuine spinGroup unitary condition. This theorem
alone does not reduce the real coefficient to either sign. -/
theorem originalSourceSpin48_trivialAction_clifford_square_eq_one
    (s : spinGroup Q)
    (hs : ∀ v : Source48Vector,
      FCP.BFSSS1V31.sourceSpin48VectorAction s v = v) :
    (s : C) * (s : C) = 1 := by
  have hstar :=
    originalSourceSpin48_trivialAction_clifford_star_fixed s hs
  have hunit : star (s : C) * (s : C) = 1 :=
    spinGroup.star_mul_self_of_mem s.property
  rw [hstar] at hunit
  exact hunit

#print axioms originalSourceSpin48_trivialAction_clifford_star_fixed
#print axioms originalSourceSpin48_trivialAction_clifford_square_eq_one

end
end FCP.BFSSS1V52K1D6
