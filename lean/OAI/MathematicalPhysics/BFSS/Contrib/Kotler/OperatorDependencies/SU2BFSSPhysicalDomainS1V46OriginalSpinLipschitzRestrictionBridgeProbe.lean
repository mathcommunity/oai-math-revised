import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V45ActualLipschitzGradeDetClosureProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V36ActualSpin48OriginalRealDeterminantCharacterProbe

/-!
S1V46 — exact original-source Spin-to-Lipschitz restriction bridge.

The TRUE Mathlib spinGroup source48Quadratic maps to the TRUE
lipschitzGroup source48Quadratic via the pinned spinGroup.toUnits and
spinGroup.units_mem_lipschitzGroup. Its Clifford conjugation action
on original Fin24 × Fin2 real labels agrees with the previously
qualified Spin-only and Lipschitz vector actions. Corresponding GL
operators and real determinant characters coincide.

No orientation+1, cover, normalized SU2 lift, manuscript intertwiner,
or physical/spectral theorem follows from this bridge alone.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V46
noncomputable section

open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev A := CliffordAlgebra Q

/-- The genuine Spin group embeds in the genuine Clifford Lipschitz subgroup,
preserving its literal original Clifford unit and group multiplication. -/
noncomputable def sourceSpin48ToActualLipschitz :
    spinGroup Q →* lipschitzGroup Q where
  toFun s := ⟨spinGroup.toUnits s, by
    apply spinGroup.units_mem_lipschitzGroup
    change (s : A) ∈ spinGroup Q
    exact s.property⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (spinGroup.toUnits : spinGroup Q →* Aˣ)
  map_mul' s t := by
    apply Subtype.ext
    exact map_mul (spinGroup.toUnits : spinGroup Q →* Aˣ) s t

/-- The original source real 48-vector actions agree on EVERY genuine
Spin element, by Clifford ι injectivity and EXACT conjugating units. -/
theorem sourceSpin48VectorAction_eq_lipschitz
    (s : spinGroup Q) (v : Source48Vector) :
    FCP.BFSSS1V31.sourceSpin48VectorAction s v =
      FCP.BFSSS1V40.sourceLipschitz48VectorAction
        (sourceSpin48ToActualLipschitz s) v := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q (FCP.BFSSS1V31.sourceSpin48VectorAction s v) =
        ConjAct.toConjAct (spinGroup.toUnits s) • (CliffordAlgebra.ι Q v) :=
      FCP.BFSSS1V31.sourceSpin48VectorAction_clifford_generator s v
    _ = ConjAct.toConjAct
          ((sourceSpin48ToActualLipschitz s : lipschitzGroup Q) : Aˣ) •
          (CliffordAlgebra.ι Q v) := rfl
    _ = CliffordAlgebra.ι Q
          (FCP.BFSSS1V40.sourceLipschitz48VectorAction
            (sourceSpin48ToActualLipschitz s) v) :=
      (FCP.BFSSS1V40.sourceLipschitz48VectorAction_clifford
        (sourceSpin48ToActualLipschitz s) v).symm

/-- Exact equality of the previously qualified original Spin-only GL48
action and the genuine Lipschitz GL48 action after restriction. -/
theorem sourceSpin48LinearEquiv_eq_lipschitz
    (s : spinGroup Q) :
    FCP.BFSSS1V34.sourceSpin48LinearEquiv s =
      FCP.BFSSS1V41.sourceLipschitz48LinearEquiv
        (sourceSpin48ToActualLipschitz s) := by
  apply LinearEquiv.ext
  intro v
  exact sourceSpin48VectorAction_eq_lipschitz s v

/-- The original S1V36 REAL Spin determinant character is exactly the
restriction of S1V41's TRUE Lipschitz determinant character. -/
theorem sourceSpin48OriginalRealDetCharacter_eq_lipschitz
    (s : spinGroup Q) :
    FCP.BFSSS1V36.sourceSpin48OriginalRealDetCharacter s =
      FCP.BFSSS1V41.sourceLipschitz48OriginalRealDetCharacter
        (sourceSpin48ToActualLipschitz s) := by
  change LinearEquiv.det (FCP.BFSSS1V34.sourceSpin48LinearEquiv s) =
    LinearEquiv.det (FCP.BFSSS1V41.sourceLipschitz48LinearEquiv
      (sourceSpin48ToActualLipschitz s))
  rw [sourceSpin48LinearEquiv_eq_lipschitz]

#print axioms sourceSpin48ToActualLipschitz
#print axioms sourceSpin48VectorAction_eq_lipschitz
#print axioms sourceSpin48LinearEquiv_eq_lipschitz
#print axioms sourceSpin48OriginalRealDetCharacter_eq_lipschitz

end
end FCP.BFSSS1V46
