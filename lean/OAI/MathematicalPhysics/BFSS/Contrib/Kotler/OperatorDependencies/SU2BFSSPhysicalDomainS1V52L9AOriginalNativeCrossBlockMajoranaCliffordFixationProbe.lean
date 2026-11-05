import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L8EOriginalOrderedSixteenNativeSU2Spin48HomProbe

/-!
S1V52-L9A — STAGED, NOT KERNEL-QUALIFIED.
Arbitrary ACTUAL original GaugeGroup2 native Spin48 image from
block β fixes a genuine source Majorana Clifford generator
in DISTINCT block α. This is the crucial cross-block locality
interface for the accepted L8E sixteen-block homomorphism.

Uses STRICT accepted L8A's genuine 48-source orthogonality,
B2's original positive-i quaternion polynomial, S1's actual
source-Clifford star conjugation, C1's genuine native SU2
unit-quaternion norm, and L7C7's exact Spin48 coe theorem.
No assumed physical Majorana conjugation, no surrogate
Clifford algebra, no assumption that all Spin48 commute.

The within-block source Clifford adjoint action and original
paired G1A Majorana label bridge remain separate obligations.
No root is qualified before a pinned strict CI plus axiom audit.
-/
set_option autoImplicit false
set_option maxHeartbeats 420000

namespace FCP.BFSSS1V52L9A
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52A
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B2
open FCP.BFSSS1V52B3
open FCP.BFSSS1V52C1
open FCP.BFSSS1V52S1
open FCP.BFSSS1V52L7C7
open FCP.BFSSS1V52L8A

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev E (α : RealSpinBlock) (i : Fin 3) : C :=
  CliffordAlgebra.ι Q (sourceBlockColorAxis α i)

/-- An arbitrary actual source Majorana generator in block α
commutes with EVERY quaternion Clifford polynomial in a
different block β, not just a chosen Z quarter rotor. -/
theorem originalNativeDisjointAxis_comm_quaternion
    (α β : RealSpinBlock) (hab : α ≠ β)
    (i : Fin 3) (p : SourceQuaternionCoords) :
    E α i * sourceCliffordQuaternion β p =
      sourceCliffordQuaternion β p * E α i := by
  have hZ :
      E α i * sourceZBivector β =
        sourceZBivector β * E α i := by
    change (E α i) * (E β 0 * E β 1) =
      (E β 0 * E β 1) * (E α i)
    exact originalDisjointBlockAxis_comm_bivector α β hab i 0 1
  have hY :
      E α i * sourceYBivector β =
        sourceYBivector β * E α i := by
    change (E α i) * (E β 2 * E β 0) =
      (E β 2 * E β 0) * (E α i)
    exact originalDisjointBlockAxis_comm_bivector α β hab i 2 0
  have hX :
      E α i * sourceXBivector β =
        sourceXBivector β * E α i := by
    change (E α i) * (E β 1 * E β 2) =
      (E β 1 * E β 2) * (E α i)
    exact originalDisjointBlockAxis_comm_bivector α β hab i 1 2
  change
    E α i * (p.a • (1 : C) + p.b • sourceZBivector β +
      p.c • sourceYBivector β + p.d • sourceXBivector β) =
    (p.a • (1 : C) + p.b • sourceZBivector β +
      p.c • sourceYBivector β + p.d • sourceXBivector β) *
      E α i
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    mul_one, one_mul, hZ, hY, hX]

/-- The source Clifford adjoint action of ANY original native
SU2 quaternion polynomial from a disjoint block is precisely
the IDENTITY on the source Majorana generator in block α.
The inverse is proved from original SOURCE quaternion
star-unitarity and genuine source SU2 norm one. -/
theorem originalNativeDisjointAxis_quaternion_conj_fixes
    (α β : RealSpinBlock) (hab : α ≠ β)
    (i : Fin 3) (g : GaugeGroup 2) :
    sourceCliffordQuaternion β (originalNativeQuaternionCoords g) *
      E α i *
      star (sourceCliffordQuaternion β (originalNativeQuaternionCoords g)) =
        E α i := by
  let p := originalNativeQuaternionCoords g
  let P : C := sourceCliffordQuaternion β p
  let V : C := E α i
  have hcomm : V * P = P * V :=
    originalNativeDisjointAxis_comm_quaternion α β hab i p
  have hnorm : sourceQuaternionNormSq p = 1 :=
    originalNativeQuaternion_norm_one g
  have hunit : P * star P = 1 :=
    sourceCliffordQuaternion_mul_star β p hnorm
  change P * V * star P = V
  calc
    P * V * star P = V * (P * star P) := by
      rw [← hcomm]
      simp only [mul_assoc]
    _ = V := by rw [hunit, mul_one]

/-- Fully genuine Mathlib Spin48 image at disjoint block β
fixes the actual SOURCE48 original Clifford Majorana generator
of source spin block α for ANY g in original GaugeGroup2. -/
theorem originalNativeDisjointAxis_Spin48_conj_fixes
    (α β : RealSpinBlock) (hab : α ≠ β)
    (i : Fin 3) (g : GaugeGroup 2) :
    ((originalNativeGaugeSpinHom β g : spinGroup Q) : C) *
      E α i *
      star ((originalNativeGaugeSpinHom β g : spinGroup Q) : C) =
        E α i := by
  rw [originalNativeGaugeSpinHom_coe]
  exact originalNativeDisjointAxis_quaternion_conj_fixes α β hab i g

#print axioms originalNativeDisjointAxis_comm_quaternion
#print axioms originalNativeDisjointAxis_quaternion_conj_fixes
#print axioms originalNativeDisjointAxis_Spin48_conj_fixes
end
end FCP.BFSSS1V52L9A
