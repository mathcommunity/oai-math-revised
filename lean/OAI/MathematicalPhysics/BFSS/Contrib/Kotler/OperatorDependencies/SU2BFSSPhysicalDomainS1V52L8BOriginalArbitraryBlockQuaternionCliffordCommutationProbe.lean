import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L8AOriginalDisjointBlockCliffordBivectorCommutationProbe
import Mathlib.Tactic.Module

/-!
S1V52-L8B — STAGED, UNQUALIFIED, genuine original 48-Clifford
commutation of arbitrary quaternion images of two DIFFERENT
real spin blocks for ANY source quaternion coordinates p and q.

The nine cross Z/Y/X bivector commutation identities are proved
from the generic L8A source original Fin24 × Fin2 Clifford lemma,
NOT by incorrectly generalizing the historical S1V8 fixed rotor.
Only the real scalar module's rearrangement uses commutativity.
The Clifford algebra itself remains noncommutative.

This is an interface for the actual L7C7 native original SU2
Spin48 hom images and subsequent sixteen-block ordered product.
Do not count or use it before strict Lean and #print axioms PASS.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000

namespace FCP.BFSSS1V52L8B
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52A
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B2
open FCP.BFSSS1V52L8A

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev E (α : RealSpinBlock) (i : Fin 3) : C :=
  CliffordAlgebra.ι Q (sourceBlockColorAxis α i)

/-- Arbitrary real quaternion polynomials in two DISTINCT original
source three-color blocks commute INSIDE the actual original 48-real
Clifford algebra; this is NOT a CommMagma assumption on that algebra. -/
theorem originalDisjointBlockSourceQuaternion_comm
    (α β : RealSpinBlock) (hab : α ≠ β)
    (p q : SourceQuaternionCoords) :
    sourceCliffordQuaternion α p * sourceCliffordQuaternion β q =
      sourceCliffordQuaternion β q * sourceCliffordQuaternion α p := by
  have hZZ : sourceZBivector α * sourceZBivector β =
      sourceZBivector β * sourceZBivector α := by
    change (E α 0 * E α 1) * (E β 0 * E β 1) =
      (E β 0 * E β 1) * (E α 0 * E α 1)
    exact originalDisjointBlockBivectors_comm α β hab 0 1 0 1
  have hZY : sourceZBivector α * sourceYBivector β =
      sourceYBivector β * sourceZBivector α := by
    change (E α 0 * E α 1) * (E β 2 * E β 0) =
      (E β 2 * E β 0) * (E α 0 * E α 1)
    exact originalDisjointBlockBivectors_comm α β hab 0 1 2 0
  have hZX : sourceZBivector α * sourceXBivector β =
      sourceXBivector β * sourceZBivector α := by
    change (E α 0 * E α 1) * (E β 1 * E β 2) =
      (E β 1 * E β 2) * (E α 0 * E α 1)
    exact originalDisjointBlockBivectors_comm α β hab 0 1 1 2
  have hYZ : sourceYBivector α * sourceZBivector β =
      sourceZBivector β * sourceYBivector α := by
    change (E α 2 * E α 0) * (E β 0 * E β 1) =
      (E β 0 * E β 1) * (E α 2 * E α 0)
    exact originalDisjointBlockBivectors_comm α β hab 2 0 0 1
  have hYY : sourceYBivector α * sourceYBivector β =
      sourceYBivector β * sourceYBivector α := by
    change (E α 2 * E α 0) * (E β 2 * E β 0) =
      (E β 2 * E β 0) * (E α 2 * E α 0)
    exact originalDisjointBlockBivectors_comm α β hab 2 0 2 0
  have hYX : sourceYBivector α * sourceXBivector β =
      sourceXBivector β * sourceYBivector α := by
    change (E α 2 * E α 0) * (E β 1 * E β 2) =
      (E β 1 * E β 2) * (E α 2 * E α 0)
    exact originalDisjointBlockBivectors_comm α β hab 2 0 1 2
  have hXZ : sourceXBivector α * sourceZBivector β =
      sourceZBivector β * sourceXBivector α := by
    change (E α 1 * E α 2) * (E β 0 * E β 1) =
      (E β 0 * E β 1) * (E α 1 * E α 2)
    exact originalDisjointBlockBivectors_comm α β hab 1 2 0 1
  have hXY : sourceXBivector α * sourceYBivector β =
      sourceYBivector β * sourceXBivector α := by
    change (E α 1 * E α 2) * (E β 2 * E β 0) =
      (E β 2 * E β 0) * (E α 1 * E α 2)
    exact originalDisjointBlockBivectors_comm α β hab 1 2 2 0
  have hXX : sourceXBivector α * sourceXBivector β =
      sourceXBivector β * sourceXBivector α := by
    change (E α 1 * E α 2) * (E β 1 * E β 2) =
      (E β 1 * E β 2) * (E α 1 * E α 2)
    exact originalDisjointBlockBivectors_comm α β hab 1 2 1 2
  change
    (p.a • (1 : C) + p.b • sourceZBivector α +
      p.c • sourceYBivector α + p.d • sourceXBivector α) *
      (q.a • (1 : C) + q.b • sourceZBivector β +
        q.c • sourceYBivector β + q.d • sourceXBivector β) =
    (q.a • (1 : C) + q.b • sourceZBivector β +
      q.c • sourceYBivector β + q.d • sourceXBivector β) *
      (p.a • (1 : C) + p.b • sourceZBivector α +
        p.c • sourceYBivector α + p.d • sourceXBivector α)
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one,
    hZZ, hZY, hZX, hYZ, hYY, hYX, hXZ, hXY, hXX]
  module

#print axioms originalDisjointBlockSourceQuaternion_comm
end
end FCP.BFSSS1V52L8B
