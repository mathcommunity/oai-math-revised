import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9B0OriginalSameBlockBivectorAxisParityProbe

/-!
S1V52-L9B1 — staged, UNQUALIFIED source quaternion/axis reflection.
No CI is launched by this source-only staging commit.

For the actual source 48-dimensional real Clifford algebra, moving
the genuine Clifford star-conjugate of a native quaternion polynomial
across one original Majorana generator reflects exactly two of the
three imaginary quaternion coordinates. These three reflection
identities are a source-small interface from accepted S1V52S1,
the candidate nine parity roots L9B0, and the original quaternion
polynomial B2. They do NOT imply the full conjugation coefficient
theorem until the accepted quaternion multiplication law is applied,
and they do NOT establish adjointColorMatrix, Spin projection,
continuous lift, physical Fock identification, or spectral claims.

Strict qualification requires L9B0 to pass first, then independent
pinned-source compilation and permitted-axiom reports for all three
exact theorems. Preserve the original positive-i (Z,Y,X) order.
-/
set_option autoImplicit false
set_option maxHeartbeats 360000

namespace FCP.BFSSS1V52L9B1
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52A
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B2
open FCP.BFSSS1V52B3
open FCP.BFSSS1V52S1
open FCP.BFSSS1V52L9B0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev E (α : RealSpinBlock) (i : Fin 3) : C :=
  CliffordAlgebra.ι Q (sourceBlockColorAxis α i)

/-- e0 anticommutes with Z,Y and commutes with X.
Moving the ACTUAL source Clifford star quaternion across e0
therefore flips the imaginary X coordinate ONLY in the resulting
unstarred source quaternion polynomial. -/
theorem originalAxis0_star_quaternion_reflection
    (α : RealSpinBlock) (p : SourceQuaternionCoords) :
    E α 0 * star (sourceCliffordQuaternion α p) =
      sourceCliffordQuaternion α ⟨p.a, p.b, p.c, -p.d⟩ * E α 0 := by
  rw [sourceCliffordQuaternion_star_eq_conj]
  change
    E α 0 *
      (p.a • (1 : C) + (-p.b) • sourceZBivector α +
        (-p.c) • sourceYBivector α +
        (-p.d) • sourceXBivector α) =
    (p.a • (1 : C) + p.b • sourceZBivector α +
        p.c • sourceYBivector α +
        (-p.d) • sourceXBivector α) * E α 0
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    mul_one, one_mul,
    originalAxis0_Z_anticomm, originalAxis0_Y_anticomm,
    originalAxis0_X_comm]
  module

/-- e1 anticommutes with Z,X and commutes with Y. -/
theorem originalAxis1_star_quaternion_reflection
    (α : RealSpinBlock) (p : SourceQuaternionCoords) :
    E α 1 * star (sourceCliffordQuaternion α p) =
      sourceCliffordQuaternion α ⟨p.a, p.b, -p.c, p.d⟩ * E α 1 := by
  rw [sourceCliffordQuaternion_star_eq_conj]
  change
    E α 1 *
      (p.a • (1 : C) + (-p.b) • sourceZBivector α +
        (-p.c) • sourceYBivector α +
        (-p.d) • sourceXBivector α) =
    (p.a • (1 : C) + p.b • sourceZBivector α +
        (-p.c) • sourceYBivector α +
        p.d • sourceXBivector α) * E α 1
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    mul_one, one_mul,
    originalAxis1_Z_anticomm, originalAxis1_Y_comm,
    originalAxis1_X_anticomm]
  module

/-- e2 commutes with Z and anticommutes with Y,X. -/
theorem originalAxis2_star_quaternion_reflection
    (α : RealSpinBlock) (p : SourceQuaternionCoords) :
    E α 2 * star (sourceCliffordQuaternion α p) =
      sourceCliffordQuaternion α ⟨p.a, -p.b, p.c, p.d⟩ * E α 2 := by
  rw [sourceCliffordQuaternion_star_eq_conj]
  change
    E α 2 *
      (p.a • (1 : C) + (-p.b) • sourceZBivector α +
        (-p.c) • sourceYBivector α +
        (-p.d) • sourceXBivector α) =
    (p.a • (1 : C) + (-p.b) • sourceZBivector α +
        p.c • sourceYBivector α +
        p.d • sourceXBivector α) * E α 2
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    mul_one, one_mul,
    originalAxis2_Z_comm, originalAxis2_Y_anticomm,
    originalAxis2_X_anticomm]
  module

#print axioms originalAxis0_star_quaternion_reflection
#print axioms originalAxis1_star_quaternion_reflection
#print axioms originalAxis2_star_quaternion_reflection

end
end FCP.BFSSS1V52L9B1
