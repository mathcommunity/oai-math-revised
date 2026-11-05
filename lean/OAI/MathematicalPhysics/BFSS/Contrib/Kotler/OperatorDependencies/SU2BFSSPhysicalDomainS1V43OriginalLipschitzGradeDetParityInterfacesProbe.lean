import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V42ActualLipschitzGeneratorDeterminantProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
S1V43 — bounded grade-involute / actual Lipschitz determinant parity interfaces.

The intended universal predicate is the literal equality
  involute (↑x : CliffordAlgebra Q) = (δ_L(x) : ℝ) • (↑x : CliffordAlgebra Q)
for x in the GENUINE pinned Mathlib lipschitzGroup source48Quadratic.

Gate #1 tests exactly its value at identity, multiplicative compatibility,
and the genuine source-degree-one generators accepted in S1V42.
No unsupported induction over arbitrary group elements, no universal Spin
orientation and no covering, SU2 lift or spectral conclusions are asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V43
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V42

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- The exact parity relation, explicitly scoped to the original REAL
determinant character of the ACTUAL source Clifford Lipschitz subgroup. -/
def source48LipschitzGradeDetParity (x : lipschitzGroup Q) : Prop :=
  CliffordAlgebra.involute
      (((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) =
    ((FCP.BFSSS1V41.sourceLipschitz48OriginalRealDetCharacter x : ℝ) •
      (((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))

/-- The exact parity invariant holds at the true Lipschitz identity. -/
theorem source48LipschitzGradeDetParity_one :
    source48LipschitzGradeDetParity (1 : lipschitzGroup Q) := by
  simp [source48LipschitzGradeDetParity]

/-- The exact parity invariant is stable under the multiplication
of genuine original Clifford units. No inverse closure is assumed. -/
theorem source48LipschitzGradeDetParity_mul
    (x y : lipschitzGroup Q)
    (hx : source48LipschitzGradeDetParity x)
    (hy : source48LipschitzGradeDetParity y) :
    source48LipschitzGradeDetParity (x * y) := by
  dsimp only [source48LipschitzGradeDetParity] at hx hy ⊢
  have hc : (FCP.BFSSS1V41.sourceLipschitz48OriginalRealDetCharacter (x * y) : ℝ) =
      (FCP.BFSSS1V41.sourceLipschitz48OriginalRealDetCharacter x : ℝ) *
      (FCP.BFSSS1V41.sourceLipschitz48OriginalRealDetCharacter y : ℝ) := by
    rw [map_mul]
    rfl
  rw [hc]
  change CliffordAlgebra.involute
    ((((x : (CliffordAlgebra Q)ˣ) * (y : (CliffordAlgebra Q)ˣ)) :
      (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
    _ 
  simp only [Units.val_mul, map_mul]
  rw [hx, hy]
  exact (smul_mul_smul_comm
    (FCP.BFSSS1V41.sourceLipschitz48OriginalRealDetCharacter x : ℝ)
    (((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
    (FCP.BFSSS1V41.sourceLipschitz48OriginalRealDetCharacter y : ℝ)
    (((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))

/-- Generator-level grade/determinant compatibility for the TRUE
original Clifford unit in its TRUE Mathlib Lipschitz subgroup. -/
theorem source48LipschitzGradeDetParity_generator
    (a : Source48Vector) [Invertible (Q a)] :
    source48LipschitzGradeDetParity
      (source48CliffordGeneratorLipschitz a) := by
  dsimp only [source48LipschitzGradeDetParity]
  have hco :
      (((source48CliffordGeneratorLipschitz a :
          lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) :
          CliffordAlgebra Q) = CliffordAlgebra.ι Q a := rfl
  rw [hco, FCP.BFSSS1V42.source48ActualLipschitzGenerator_det]
  simp only [CliffordAlgebra.involute_ι, neg_one_smul]

#print axioms source48LipschitzGradeDetParity
#print axioms source48LipschitzGradeDetParity_one
#print axioms source48LipschitzGradeDetParity_mul
#print axioms source48LipschitzGradeDetParity_generator

end
end FCP.BFSSS1V43
