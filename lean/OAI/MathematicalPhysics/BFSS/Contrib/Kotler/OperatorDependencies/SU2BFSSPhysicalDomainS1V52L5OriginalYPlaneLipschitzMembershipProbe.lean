import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L4OriginalColorPlaneRotorGeometryProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

/-!
S1V52-L5: STAGED UNQUALIFIED genuine source-48 LipschitzGroup membership
for normalized Y-plane quaternion polynomial in actual ORIGINAL
48-dimensional Clifford algebra (NOT a surrogate Spin(3) model).

Qualified L4 supplies Q-norm-one source vector c*e2-s*e0 and its EXACT Clifford
factorization with the literal original +i Y-bivector. This module constructs
two actual units of the original Clifford algebra whose coerced
values are genuine canonical `CliffordAlgebra.ι source48Quadratic`
vectors. The pinned Mathlib Lipschitz definition is precisely
`Subgroup.closure ((↑) ⁻¹' Set.range (ι Q))`; hence the product of
these units is in the genuine group by subgroup closure.

This is an independently staged Y-plane candidate and is UNQUALIFIED
until strict pinned CI compiler and axiom checks. The all-native original
SU2 ZYZ factorization and Spin membership remain separate obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 470000

namespace FCP.BFSSS1V52L5
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52A
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B2
open FCP.BFSSS1V52B3
open FCP.BFSSS1V52L1A
open FCP.BFSSS1V52L4

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- First original-source Clifford generator unit in the Y plane,
with its inverse exactly equal to itself by Q(v)=1. -/
noncomputable def sourceYPlaneFirstUnit (α : RealSpinBlock)
    (c s : ℝ) (hcs : c*c + s*s = 1) : Cˣ := by
  -- Use the literal original 48-Majorana source expression,
  -- avoiding the let-bound local norm unification that Gate L1#1
  -- proved too expensive for elaboration.
  have hsq :
      CliffordAlgebra.ι Q
        (c • sourceBlockColorAxis α 2 - s • sourceBlockColorAxis α 0) *
      CliffordAlgebra.ι Q
        (c • sourceBlockColorAxis α 2 - s • sourceBlockColorAxis α 0) =
      (1 : C) := by
    rw [CliffordAlgebra.ι_sq_scalar,
      sourceColorPlane_firstVector_unit α 2 0 (by decide) c s hcs, map_one]
  exact ⟨CliffordAlgebra.ι Q
            (c • sourceBlockColorAxis α 2 - s • sourceBlockColorAxis α 0),
         CliffordAlgebra.ι Q
            (c • sourceBlockColorAxis α 2 - s • sourceBlockColorAxis α 0),
         hsq, hsq⟩

theorem sourceYPlaneFirstUnit_coe (α : RealSpinBlock)
    (c s : ℝ) (hcs : c*c + s*s = 1) :
    (sourceYPlaneFirstUnit α c s hcs : C) =
      CliffordAlgebra.ι Q
        (c • sourceBlockColorAxis α 2 - s • sourceBlockColorAxis α 0) := rfl

/-- The second original Clifford generator unit of the Y plane. -/
noncomputable def sourceYPlaneFixedUnit (α : RealSpinBlock) : Cˣ :=
  ⟨CliffordAlgebra.ι Q (sourceBlockColorAxis α 2),
    CliffordAlgebra.ι Q (sourceBlockColorAxis α 2),
    sourceAxis_square α 2, sourceAxis_square α 2⟩

theorem sourceYPlaneFixedUnit_coe (α : RealSpinBlock) :
    (sourceYPlaneFixedUnit α : C) =
      CliffordAlgebra.ι Q (sourceBlockColorAxis α 2) := rfl

/-- Actual subgroup-closure proof from the genuine original Q-vector
generator, not from ambient unit invertibility alone. -/
theorem sourceYPlaneFirstUnit_mem_lipschitz
    (α : RealSpinBlock) (c s : ℝ) (hcs : c*c+s*s=1) :
    sourceYPlaneFirstUnit α c s hcs ∈ lipschitzGroup Q := by
  apply Subgroup.subset_closure
  change (sourceYPlaneFirstUnit α c s hcs : C) ∈
    Set.range (CliffordAlgebra.ι Q)
  exact ⟨_, sourceYPlaneFirstUnit_coe α c s hcs⟩

theorem sourceYPlaneFixedUnit_mem_lipschitz (α : RealSpinBlock) :
    sourceYPlaneFixedUnit α ∈ lipschitzGroup Q := by
  apply Subgroup.subset_closure
  change (sourceYPlaneFixedUnit α : C) ∈
    Set.range (CliffordAlgebra.ι Q)
  exact ⟨_, sourceYPlaneFixedUnit_coe α⟩

/-- A normalized source positive-i Y quaternion belongs to the
genuine pinned Mathlib Lipschitz subgroup of source48Quadratic. -/
theorem sourceYPlaneQuaternionUnit_mem_lipschitz
    (α : RealSpinBlock) (c s : ℝ) (hcs : c*c+s*s=1)
    (hp : sourceQuaternionNormSq
      (⟨c,0,s,0⟩ : SourceQuaternionCoords) = 1) :
    sourceCliffordQuaternionUnit α ⟨c,0,s,0⟩ hp ∈
      lipschitzGroup Q := by
  have hunit :
      sourceCliffordQuaternionUnit α ⟨c,0,s,0⟩ hp =
        sourceYPlaneFirstUnit α c s hcs *
          sourceYPlaneFixedUnit α := by
    apply Units.ext
    change sourceCliffordQuaternion α ⟨c,0,s,0⟩ =
      CliffordAlgebra.ι Q
        (c • sourceBlockColorAxis α 2 - s • sourceBlockColorAxis α 0) *
      CliffordAlgebra.ι Q (sourceBlockColorAxis α 2)
    rw [sourceYPlane_twoVector_factor]
    simp [sourceCliffordQuaternion]
  rw [hunit]
  exact mul_mem
    (sourceYPlaneFirstUnit_mem_lipschitz α c s hcs)
    (sourceYPlaneFixedUnit_mem_lipschitz α)

#print axioms sourceYPlaneFirstUnit
#print axioms sourceYPlaneFirstUnit_coe
#print axioms sourceYPlaneFixedUnit
#print axioms sourceYPlaneFixedUnit_coe
#print axioms sourceYPlaneFirstUnit_mem_lipschitz
#print axioms sourceYPlaneFixedUnit_mem_lipschitz
#print axioms sourceYPlaneQuaternionUnit_mem_lipschitz

end
end FCP.BFSSS1V52L5
