import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L8BOriginalArbitraryBlockQuaternionCliffordCommutationProbe

/-!
S1V52-L8C — STAGED / UNQUALIFIED true source Spin48 subgroup
cross-block commutation of ARBITRARY native original SU2 images.

No globally commutative Spin48 assumption. We will apply the
previously accepted L7C7 per-block true original
`GaugeGroup 2 →* spinGroup source48Quadratic` hom with B2's
exact source polynomial coe and L8B's true source 48-Clifford
arbitrary cross-block polynomial commutation.

Requires L8A and L8B strict acceptance before qualifying L8C.
This still is NOT the sixteen-block product group hom.
-/
set_option autoImplicit false
set_option maxHeartbeats 360000

namespace FCP.BFSSS1V52L8C
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52B2
open FCP.BFSSS1V52C1
open FCP.BFSSS1V52L7C7
open FCP.BFSSS1V52L8B

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- For ANY actual original SU2 gauge elements g and h, their
qualified native original Spin48 lifts at two distinct real
spin blocks commute INSIDE the true Mathlib spinGroup Q. -/
theorem originalNativeSpinHom_crossBlock_comm
    (α β : RealSpinBlock) (hab : α ≠ β)
    (g h : GaugeGroup 2) :
    originalNativeGaugeSpinHom α g * originalNativeGaugeSpinHom β h =
      originalNativeGaugeSpinHom β h * originalNativeGaugeSpinHom α g := by
  apply Subtype.ext
  change
    ((originalNativeGaugeSpinHom α g : spinGroup Q) : C) *
      ((originalNativeGaugeSpinHom β h : spinGroup Q) : C) =
    ((originalNativeGaugeSpinHom β h : spinGroup Q) : C) *
      ((originalNativeGaugeSpinHom α g : spinGroup Q) : C)
  rw [originalNativeGaugeSpinHom_coe, originalNativeGaugeSpinHom_coe]
  exact originalDisjointBlockSourceQuaternion_comm α β hab
    (originalNativeQuaternionCoords g) (originalNativeQuaternionCoords h)

#print axioms originalNativeSpinHom_crossBlock_comm

end
end FCP.BFSSS1V52L8C
