import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9D2OriginalNativeSameBlockSpin48RealVectorActionProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9D3OriginalNativeDisjointBlockSpin48RealVectorFixationProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V32AllSpin48CanonicalVectorLinearGroupActionProbe

/-!
S1V52L9D4 — STAGED, UNQUALIFIED generic original source-block
real Spin(48) action interfaces for the future ordered 16-factor
native SU2 source projection theorem.

L9D2 provides three actual source 48-real same-block action roots;
L9D3 proposes the independently testable arbitrary distinct-block
real-vector fixation; S1V31/S1V32 accepted the original 48-real
Spin-vector linearity and group multiplication. Here we package
the three color axes as an exact finite sum and show any disjoint
native block Spin(48) element fixes *all* color combinations from
another source block. Both claims preserve original native gauge,
Fin3 color, output/input order and 48-real source vectors.

No 16-block product or original Fock matrix equality is claimed here;
the new roots remain unqualified before their own strict pinned CI.
-/

set_option autoImplicit false
set_option maxHeartbeats 280000

namespace FCP.BFSSS1V52L9D4
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L7C7
open FCP.BFSSS1V52L9D2
open FCP.BFSSS1V52L9D3
open FCP.BFSSSU2GaugeG3A

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Uniform exact real 48-vector local source Spin action for any
original input color axis, not an independent 3D representation. -/
theorem originalNativeSameBlockSpin48Vector_axis_all
    (α : RealSpinBlock) (g : GaugeGroup 2) (A : Fin 3) :
    FCP.BFSSS1V31.sourceSpin48VectorAction
      (originalNativeGaugeSpinHom α g) (sourceBlockColorAxis α A) =
      ∑ B : Fin 3,
        (adjointColorMatrix g B A) • sourceBlockColorAxis α B := by
  -- Fin.cases exposes constructor proof terms ⟨0, _⟩, etc.
  -- Full Fin simplification identifies these with the *original*
  -- numeral-index source theorem, not an altered color representation.
  fin_cases A
  · simpa [Fin.sum_univ_three] using
      (originalNativeSameBlockSpin48Vector_axis0 α g)
  · simpa [Fin.sum_univ_three] using
      (originalNativeSameBlockSpin48Vector_axis1 α g)
  · simpa [Fin.sum_univ_three] using
      (originalNativeSameBlockSpin48Vector_axis2 α g)

/-- Crucial induction invariant for ordered sixteen-block projection:
any native SU2 Spin(48) rotor in different block β fixes an arbitrary
REAL linear combination of source Majorana axes in block α. -/
theorem originalNativeDisjointBlockSpin48Vector_fixes_colorCombination
    (α β : RealSpinBlock) (hab : α ≠ β)
    (g : GaugeGroup 2) (c : Fin 3 → ℝ) :
    FCP.BFSSS1V31.sourceSpin48VectorAction
      (originalNativeGaugeSpinHom β g)
      (∑ A : Fin 3, c A • sourceBlockColorAxis α A) =
      ∑ A : Fin 3, c A • sourceBlockColorAxis α A := by
  -- First distribute the genuine source Spin48 action over the
  -- three REAL color components. The distinct-block hypothesis
  -- must be passed explicitly in each source fixation rewrite.
  simp only [Fin.sum_univ_three,
    FCP.BFSSS1V31.sourceSpin48VectorAction_add,
    FCP.BFSSS1V32.sourceSpin48VectorAction_smul]
  rw [originalNativeDisjointBlockSpin48Vector_fixes α β hab 0 g,
      originalNativeDisjointBlockSpin48Vector_fixes α β hab 1 g,
      originalNativeDisjointBlockSpin48Vector_fixes α β hab 2 g]

#print axioms originalNativeSameBlockSpin48Vector_axis_all
#print axioms originalNativeDisjointBlockSpin48Vector_fixes_colorCombination

end
end FCP.BFSSS1V52L9D4
