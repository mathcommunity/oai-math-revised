import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F1OriginalCliffordEvenFockStarMultiplicativeClosureProbe

/-!
S1V52L9E5F2 — STAGED / UNQUALIFIED original finite ordered
source Clifford bivector word star-to-Fock-adjoint transport.

Original input is a list of pairs of ORIGINAL 48-real-source
vectors; each pair means the ACTUAL source Clifford product
ι(u)*ι(v). This is not a surrogate Clifford representation.

The prior E3 theorem is proved on EVERY original bivector
pair; the prior F1 theorem is conditional multiplicative
closure. Induction on the list of pairs yields a finite-word
result with actual multiplication ORDER preserved.

No assertion of global odd Clifford star preservation,
full even Clifford linear span, or native Spin48 Fock unitary.
-/

set_option autoImplicit false
set_option maxHeartbeats 320000

namespace FCP.BFSSS1V52L9E5F2
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5E3
open FCP.BFSSS1V52L9E5F1

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- A single actual original degree-two Clifford product. -/
private abbrev sourceBivector (p : Source48Vector × Source48Vector) : C :=
  CliffordAlgebra.ι Q p.1 * CliffordAlgebra.ι Q p.2

/-- The original Fock Clifford algebra map respects the two
star operations on the identity. This is the true empty-word
base; no source Clifford parity shortcut. -/
theorem originalFockCliffordAlgHom_star_one :
    originalFockCliffordAlgHom (star (1 : C)) =
      star (originalFockCliffordAlgHom (1 : C)) := by
  simp only [star_one, map_one]

/-- Every FINITE ORDERED product of actual original
Clifford bivectors is star/Fock-adjoint compatible.
The Clifford star compatibility is only asserted for
these even words, NOT arbitrary odd Clifford elements. -/
theorem originalFockCliffordAlgHom_star_bivectorWord
    (pairs : List (Source48Vector × Source48Vector)) :
    originalFockCliffordAlgHom
      (star ((pairs.map sourceBivector).prod)) =
    star (originalFockCliffordAlgHom
      ((pairs.map sourceBivector).prod)) := by
  induction pairs with
  | nil =>
      simpa only [List.map_nil, List.prod_nil] using
        originalFockCliffordAlgHom_star_one
  | cons p ps ih =>
      simpa only [List.map_cons, List.prod_cons] using
        (originalFockCliffordAlgHom_star_mul_of
          (sourceBivector p)
          ((ps.map sourceBivector).prod)
          (originalFockCliffordAlgHom_star_sourceBivector p.1 p.2)
          ih)

#print axioms originalFockCliffordAlgHom_star_one
#print axioms originalFockCliffordAlgHom_star_bivectorWord

end
end FCP.BFSSS1V52L9E5F2
