import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L1DOriginalZPlaneSourceAxisUnitProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

/-!
S1V52-L2: SOURCE-EXACT candidate genuine LipschitzGroup membership
for normalized Z-plane quaternion polynomial in actual ORIGINAL
48-dimensional Clifford algebra (NOT a surrogate Spin(3) model).

Qualified L1D supplies Q-norm-one source vector c*e0-s*e1 and its EXACT Clifford
factorization with original +i Z-bivector. This module constructs
two actual units of the original Clifford algebra whose coerced
values are genuine canonical `CliffordAlgebra.ι source48Quadratic`
vectors. The pinned Mathlib Lipschitz definition is precisely
`Subgroup.closure ((↑) ⁻¹' Set.range (ι Q))`; hence the product of
these units is in the genuine group by subgroup closure.

This revised L2 source retains the prior source-exact theorem statements and is
UNQUALIFIED until independent pinned CI compiler and axiom checks.
Its theorem is ONLY the Z-plane; Y-plane and exact ZYZ factorization
of ALL native GaugeGroup 2 elements must be proved separately.
-/

set_option autoImplicit false
set_option maxHeartbeats 470000

namespace FCP.BFSSS1V52L2
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52A
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B2
open FCP.BFSSS1V52B3
open FCP.BFSSS1V52L1A
open FCP.BFSSS1V52L1D

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- First original-source Clifford generator unit in the Z plane,
with its inverse exactly equal to itself by Q(v)=1. -/
noncomputable def sourceZPlaneFirstUnit (α : RealSpinBlock)
    (c s : ℝ) (hcs : c*c + s*s = 1) : Cˣ := by
  -- Use the literal original 48-Majorana source expression,
  -- avoiding the let-bound local norm unification that Gate L1#1
  -- proved too expensive for elaboration.
  have hsq :
      CliffordAlgebra.ι Q
        (c • sourceBlockColorAxis α 0 - s • sourceBlockColorAxis α 1) *
      CliffordAlgebra.ι Q
        (c • sourceBlockColorAxis α 0 - s • sourceBlockColorAxis α 1) =
      (1 : C) := by
    rw [CliffordAlgebra.ι_sq_scalar,
      sourceZPlane_firstVector_unit α c s hcs, map_one]
  exact ⟨CliffordAlgebra.ι Q
            (c • sourceBlockColorAxis α 0 - s • sourceBlockColorAxis α 1),
         CliffordAlgebra.ι Q
            (c • sourceBlockColorAxis α 0 - s • sourceBlockColorAxis α 1),
         hsq, hsq⟩

theorem sourceZPlaneFirstUnit_coe (α : RealSpinBlock)
    (c s : ℝ) (hcs : c*c + s*s = 1) :
    (sourceZPlaneFirstUnit α c s hcs : C) =
      CliffordAlgebra.ι Q
        (c • sourceBlockColorAxis α 0 - s • sourceBlockColorAxis α 1) := rfl

/-- The second original Clifford generator unit of the Z plane. -/
noncomputable def sourceZPlaneFixedUnit (α : RealSpinBlock) : Cˣ :=
  ⟨CliffordAlgebra.ι Q (sourceBlockColorAxis α 0),
    CliffordAlgebra.ι Q (sourceBlockColorAxis α 0),
    sourceAxis_square α 0, sourceAxis_square α 0⟩

theorem sourceZPlaneFixedUnit_coe (α : RealSpinBlock) :
    (sourceZPlaneFixedUnit α : C) =
      CliffordAlgebra.ι Q (sourceBlockColorAxis α 0) := rfl

/-- Actual subgroup-closure proof from the genuine original Q-vector
generator, not from ambient unit invertibility alone. -/
theorem sourceZPlaneFirstUnit_mem_lipschitz
    (α : RealSpinBlock) (c s : ℝ) (hcs : c*c+s*s=1) :
    sourceZPlaneFirstUnit α c s hcs ∈ lipschitzGroup Q := by
  apply Subgroup.subset_closure
  change (sourceZPlaneFirstUnit α c s hcs : C) ∈
    Set.range (CliffordAlgebra.ι Q)
  exact ⟨_, sourceZPlaneFirstUnit_coe α c s hcs⟩

theorem sourceZPlaneFixedUnit_mem_lipschitz (α : RealSpinBlock) :
    sourceZPlaneFixedUnit α ∈ lipschitzGroup Q := by
  apply Subgroup.subset_closure
  change (sourceZPlaneFixedUnit α : C) ∈
    Set.range (CliffordAlgebra.ι Q)
  exact ⟨_, sourceZPlaneFixedUnit_coe α⟩

/-- A normalized source positive-i Z quaternion belongs to the
genuine pinned Mathlib Lipschitz subgroup of source48Quadratic. -/
theorem sourceZPlaneQuaternionUnit_mem_lipschitz
    (α : RealSpinBlock) (c s : ℝ) (hcs : c*c+s*s=1)
    (hp : sourceQuaternionNormSq
      (⟨c,s,0,0⟩ : SourceQuaternionCoords) = 1) :
    sourceCliffordQuaternionUnit α ⟨c,s,0,0⟩ hp ∈
      lipschitzGroup Q := by
  have hunit :
      sourceCliffordQuaternionUnit α ⟨c,s,0,0⟩ hp =
        sourceZPlaneFirstUnit α c s hcs *
          sourceZPlaneFixedUnit α := by
    apply Units.ext
    change sourceCliffordQuaternion α ⟨c,s,0,0⟩ =
      CliffordAlgebra.ι Q
        (c • sourceBlockColorAxis α 0 - s • sourceBlockColorAxis α 1) *
      CliffordAlgebra.ι Q (sourceBlockColorAxis α 0)
    rw [sourceZPlane_twoVector_factor]
    simp [sourceCliffordQuaternion]
  rw [hunit]
  exact mul_mem
    (sourceZPlaneFirstUnit_mem_lipschitz α c s hcs)
    (sourceZPlaneFixedUnit_mem_lipschitz α)

#print axioms sourceZPlaneFirstUnit
#print axioms sourceZPlaneFirstUnit_coe
#print axioms sourceZPlaneFixedUnit
#print axioms sourceZPlaneFixedUnit_coe
#print axioms sourceZPlaneFirstUnit_mem_lipschitz
#print axioms sourceZPlaneFixedUnit_mem_lipschitz
#print axioms sourceZPlaneQuaternionUnit_mem_lipschitz

end
end FCP.BFSSS1V52L2
