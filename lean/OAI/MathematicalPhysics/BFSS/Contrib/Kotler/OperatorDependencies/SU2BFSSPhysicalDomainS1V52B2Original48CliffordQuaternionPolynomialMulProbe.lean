import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52B1SourcePauliQuaternionMatrixMultiplicationProbe
import Mathlib.Tactic.Module

/-!
S1V52-B2 — CANDIDATE multiplicativity of the real quaternion polynomial
INSIDE the genuine original 48-dimensional real source Clifford algebra.

This bridges two strictly accepted finite statements:
S1V52A: 48-source even-Clifford Z,Y,X quaternion multiplication table.
S1V52B1: identical real quaternion coefficients multiply the literal
original-sized +i Pauli 2x2 matrices.

No alternate SU2 group and no 3D Clifford surrogate: the target uses
CliffordAlgebra source48Quadratic on the actual Fin24 × Fin2 real
Majorana labels. This gate proves algebraic polynomial multiplicativity;
native GaugeGroup 2 extraction, actual spinGroup membership, continuous
16-block lift and original Pauli adjoint projection remain independent.

CANDIDATE until strictly kernel-compiled and #print axioms accepted.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52B2
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52A
open FCP.BFSSS1V52B1

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- The ORIGINAL-SOURCE 48-real even Clifford polynomial, using the
same positive-i quaternion coordinate order (Z,Y,X) as B1. -/
noncomputable def sourceCliffordQuaternion
    (α : RealSpinBlock) (p : SourceQuaternionCoords) : C :=
  p.a • (1 : C) +
  p.b • sourceZBivector α +
  p.c • sourceYBivector α +
  p.d • sourceXBivector α

/-- Identity coordinate quaternion is literally the source 48 Clifford
identity. No claim of global source Spin membership is inserted. -/
theorem sourceCliffordQuaternion_one (α : RealSpinBlock) :
    sourceCliffordQuaternion α sourceQuaternionOne = 1 := by
  simp [sourceCliffordQuaternion, sourceQuaternionOne]

/-- For any two real source quaternion-coordinate quadruples the
polynomial in the GENUINE source 48-Clifford algebra is
multiplication-preserving. All nine bivector products are replaced by
the qualified S1V52A identities; scalar coefficients are then verified
by Mathlib's module tactic over the COMMUTATIVE scalar ring ℝ, while
the Clifford multiplication itself is NEVER treated as commutative. -/
theorem sourceCliffordQuaternion_compose
    (α : RealSpinBlock) (p q : SourceQuaternionCoords) :
    sourceCliffordQuaternion α (sourceQuaternionCompose p q) =
      sourceCliffordQuaternion α p * sourceCliffordQuaternion α q := by
  let Z : C := sourceZBivector α
  let Y : C := sourceYBivector α
  let X : C := sourceXBivector α
  have hZZ : Z * Z = -1 := sourceZBivector_square α
  have hYY : Y * Y = -1 := sourceYBivector_square α
  have hXX : X * X = -1 := sourceXBivector_square α
  have hZY : Z * Y = X := sourceZ_mul_Y α
  have hYX : Y * X = Z := sourceY_mul_X α
  have hXZ : X * Z = Y := sourceX_mul_Z α
  have hYZ : Y * Z = -X := sourceY_mul_Z α
  have hXY : X * Y = -Z := sourceX_mul_Y α
  have hZX : Z * X = -Y := sourceZ_mul_X α
  change
    (p.a*q.a - p.b*q.b - p.c*q.c - p.d*q.d) • (1 : C) +
      (p.a*q.b + p.b*q.a + p.c*q.d - p.d*q.c) • Z +
      (p.a*q.c + p.c*q.a + p.d*q.b - p.b*q.d) • Y +
      (p.a*q.d + p.d*q.a + p.b*q.c - p.c*q.b) • X =
    (p.a • (1 : C) + p.b • Z + p.c • Y + p.d • X) *
      (q.a • (1 : C) + q.b • Z + q.c • Y + q.d • X)
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_smul, one_mul, mul_one,
    hZZ, hYY, hXX, hZY, hYX, hXZ, hYZ, hXY, hZX,
    smul_neg, smul_one]
  module

#print axioms sourceCliffordQuaternion_one
#print axioms sourceCliffordQuaternion_compose

end
end FCP.BFSSS1V52B2
