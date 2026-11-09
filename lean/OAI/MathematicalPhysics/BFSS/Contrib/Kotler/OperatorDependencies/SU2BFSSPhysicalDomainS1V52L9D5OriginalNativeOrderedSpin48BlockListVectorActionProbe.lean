import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9D4OriginalNativeBlockSpin48RealVectorColorCombinationProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L8DOriginalNodupNativeBlockSpin48ListHomProbe

/-!
S1V52L9D5 — STAGED, UNQUALIFIED generic ordered source Spin(48)
list-product real 48-vector action for the actual native BFSS SU(2).

This module is explicitly downstream of the NOT-YET-QUALIFIED L9D4
source color-combination interface. It does not rely on a
commutative target Spin group. Proofs are inductions on List.prod
of genuine source block homomorphisms and use the accepted source
Spin48 action-multiplication rule, exact same-block BFSS adjoint,
and disjoint-block fixation.

Three candidate roots: any disjoint ordered block list fixes a
source Majorana axis; it fixes a whole original color combination;
and any Nodup source ordered list containing block α induces the
actual original color-adjoint rotation on block α.

These alone do NOT prove sourceRealMajoranaMatrix equality or
sourceSpin48CoversActualGauge. Both remain future obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52L9D5
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L7C7
open FCP.BFSSS1V52L8D
open FCP.BFSSS1V52L9D3
open FCP.BFSSS1V52L9D4
open FCP.BFSSSU2GaugeG3A

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- An ordered finite product of actual native Spin(48) elements
from blocks all DIFFERENT from α fixes its source real axis. -/
theorem originalNativeBlockSpinProd_disjoint_fixes_axis
    (α : RealSpinBlock) (g : GaugeGroup 2) (A : Fin 3) :
    ∀ xs : List RealSpinBlock, α ∉ xs →
    FCP.BFSSS1V31.sourceSpin48VectorAction
      (originalNativeBlockSpinProd xs g)
      (sourceBlockColorAxis α A) = sourceBlockColorAxis α A := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simpa [originalNativeBlockSpinProd] using
        (FCP.BFSSS1V32.sourceSpin48VectorAction_one
          (sourceBlockColorAxis α A))
  | cons β xs ih =>
      intro hnot
      have hab : α ≠ β := by
        intro heq
        apply hnot
        simp [heq]
      have htail : α ∉ xs := by
        intro hm
        apply hnot
        simp [hm]
      change FCP.BFSSS1V31.sourceSpin48VectorAction
        (originalNativeGaugeSpinHom β g * originalNativeBlockSpinProd xs g)
        (sourceBlockColorAxis α A) = sourceBlockColorAxis α A
      rw [FCP.BFSSS1V32.sourceSpin48VectorAction_mul, ih htail]
      exact originalNativeDisjointBlockSpin48Vector_fixes α β hab A g

/-- A product of rotations in blocks other than α fixes every
real combination of original α-block color Majorana axes. -/
theorem originalNativeBlockSpinProd_disjoint_fixes_colorCombination
    (α : RealSpinBlock) (g : GaugeGroup 2)
    (c : Fin 3 → ℝ) :
    ∀ xs : List RealSpinBlock, α ∉ xs →
    FCP.BFSSS1V31.sourceSpin48VectorAction
      (originalNativeBlockSpinProd xs g)
      (∑ A : Fin 3, c A • sourceBlockColorAxis α A) =
        ∑ A : Fin 3, c A • sourceBlockColorAxis α A := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simpa [originalNativeBlockSpinProd] using
        (FCP.BFSSS1V32.sourceSpin48VectorAction_one
          (∑ A : Fin 3, c A • sourceBlockColorAxis α A))
  | cons β xs ih =>
      intro hnot
      have hab : α ≠ β := by
        intro heq
        apply hnot
        simp [heq]
      have htail : α ∉ xs := by
        intro hm
        apply hnot
        simp [hm]
      change FCP.BFSSS1V31.sourceSpin48VectorAction
        (originalNativeGaugeSpinHom β g * originalNativeBlockSpinProd xs g)
        (∑ A : Fin 3, c A • sourceBlockColorAxis α A) =
          ∑ A : Fin 3, c A • sourceBlockColorAxis α A
      rw [FCP.BFSSS1V32.sourceSpin48VectorAction_mul, ih htail]
      exact originalNativeDisjointBlockSpin48Vector_fixes_colorCombination
        α β hab g c

/-- The exact BFSS native SU(2) color-adjoint action is reproduced
on α's axis by ANY original ordered Nodup Spin(48) block list
containing α; this is not restricted to a convenient order. -/
theorem originalNativeBlockSpinProd_member_action
    (α : RealSpinBlock) (g : GaugeGroup 2) (A : Fin 3) :
    ∀ xs : List RealSpinBlock, xs.Nodup → α ∈ xs →
      FCP.BFSSS1V31.sourceSpin48VectorAction
        (originalNativeBlockSpinProd xs g)
        (sourceBlockColorAxis α A) =
      ∑ B : Fin 3,
        (adjointColorMatrix g B A) • sourceBlockColorAxis α B := by
  intro xs
  induction xs with
  | nil =>
      intro _ hmem
      simp at hmem
  | cons β xs ih =>
      intro hnodup hmem
      have htail : xs.Nodup := (List.nodup_cons.mp hnodup).2
      have hnot : β ∉ xs := (List.nodup_cons.mp hnodup).1
      have hcons :
          originalNativeBlockSpinProd (β :: xs) g =
            originalNativeGaugeSpinHom β g *
              originalNativeBlockSpinProd xs g := rfl
      rw [hcons, FCP.BFSSS1V32.sourceSpin48VectorAction_mul]
      rcases List.mem_cons.mp hmem with hhead | hrest
      · subst β
        rw [originalNativeBlockSpinProd_disjoint_fixes_axis α g A xs hnot]
        exact originalNativeSameBlockSpin48Vector_axis_all α g A
      · have hab : α ≠ β := by
          intro heq
          subst β
          exact hnot hrest
        rw [ih htail hrest]
        exact originalNativeDisjointBlockSpin48Vector_fixes_colorCombination
          α β hab g (fun B => adjointColorMatrix g B A)

#print axioms originalNativeBlockSpinProd_disjoint_fixes_axis
#print axioms originalNativeBlockSpinProd_disjoint_fixes_colorCombination
#print axioms originalNativeBlockSpinProd_member_action

end
end FCP.BFSSS1V52L9D5
