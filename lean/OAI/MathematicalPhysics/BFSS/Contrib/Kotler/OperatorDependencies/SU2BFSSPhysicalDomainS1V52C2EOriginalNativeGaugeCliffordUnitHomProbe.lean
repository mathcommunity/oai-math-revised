import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52C2DOriginalNativeSU2QuaternionMultiplicationProbe

/-!
S1V52-C2E: exact original BFSS GaugeGroup 2 to genuine original
48-Majorana source Clifford ALGEBRA UNITS monoid homomorphism on
an arbitrary fixed original spin block.

This is NOT a map to Mathlib spinGroup, even when it is accepted:
genuine lipschitzGroup, star unitary, evenness, source adjoint action
and continuity remain separate exact-source obligations.

Depends on C2D native real quaternion multiplication, NOT qualified
until C2D strict CI succeeds. Source candidate only; no assumed axioms.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52C2E
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B2
open FCP.BFSSS1V52B3
open FCP.BFSSS1V52C1
open FCP.BFSSS1V52C2D

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Identity of the native SU2 group has the expected exact
positive-i quaternion coefficient tuple. -/
theorem originalNativeQuaternionCoords_one :
    originalNativeQuaternionCoords (1 : GaugeGroup 2) =
      sourceQuaternionOne := by
  simp [originalNativeQuaternionCoords, sourceQuaternionOne,
    Matrix.one_apply]

/-- The genuine ORIGINAL-source Clifford algebra unit with norm-one
certificate from the native source BFSS SU2 matrix. -/
noncomputable def originalNativeGaugeSourceCliffordUnit
    (α : RealSpinBlock) (g : GaugeGroup 2) : Cˣ :=
  sourceCliffordQuaternionUnit α
    (originalNativeQuaternionCoords g)
    (originalNativeQuaternion_norm_one g)

/-- The native source SU2 group acts as a blockwise Clifford-UNIT
monoid homomorphism. This is weaker than Spin membership. -/
noncomputable def originalNativeGaugeSourceCliffordUnitHom
    (α : RealSpinBlock) : GaugeGroup 2 →* Cˣ where
  toFun := originalNativeGaugeSourceCliffordUnit α
  map_one' := by
    apply Units.ext
    change sourceCliffordQuaternion α
      (originalNativeQuaternionCoords (1 : GaugeGroup 2)) = (1 : C)
    rw [originalNativeQuaternionCoords_one]
    exact sourceCliffordQuaternion_one α
  map_mul' g h := by
    apply Units.ext
    change sourceCliffordQuaternion α
      (originalNativeQuaternionCoords (g * h)) =
      sourceCliffordQuaternion α (originalNativeQuaternionCoords g) *
        sourceCliffordQuaternion α (originalNativeQuaternionCoords h)
    rw [originalNativeQuaternionCoords_mul]
    exact sourceCliffordQuaternion_compose α
      (originalNativeQuaternionCoords g)
      (originalNativeQuaternionCoords h)

/-- State explicitly that the monoid homomorphism's ambient Clifford
coercion is the original 48-source quaternion polynomial. -/
theorem originalNativeGaugeSourceCliffordUnitHom_coe
    (α : RealSpinBlock) (g : GaugeGroup 2) :
    ((originalNativeGaugeSourceCliffordUnitHom α g : Cˣ) : C) =
      sourceCliffordQuaternion α (originalNativeQuaternionCoords g) := rfl

#print axioms originalNativeQuaternionCoords_one
#print axioms originalNativeGaugeSourceCliffordUnit
#print axioms originalNativeGaugeSourceCliffordUnitHom
#print axioms originalNativeGaugeSourceCliffordUnitHom_coe

end
end FCP.BFSSS1V52C2E
