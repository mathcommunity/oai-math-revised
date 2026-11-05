import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L1AIsolatedAbstractNormAndOriginalZCliffordFactorProbe

/-!
S1V52L1C — isolated TWO-ROOT strict candidate, extracted from L1B
Gate #3 negative knowledge.

1) Genuine 48-label dotProduct two-coordinate norm.
2) Transport from dotProduct via the accepted S1V6 theorem
   source48Quadratic_eq_dot, retaining EXACT original source Q.

The original block-axis specialization that exceeded recursion in L1B
Gate #3 has been intentionally REMOVED. NO claim that a native
Z-plane source vector has norm 1, or that its unit belongs to
lipschitzGroup/spinGroup, until a separate strictly qualified proof.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000

namespace FCP.BFSSS1V52L1C
noncomputable section
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V6
open Matrix

/-- Dot-product squared norm of two distinct ORIGINAL 48-label
Pi.single coordinates.  The result is proved purely by finite
coordinate arithmetic, NOT by elaborating source48Quadratic. -/
theorem source48Dot_two_coordinate_norm
    (i j : SourceLabel) (hij : i ≠ j) (c s : ℝ) :
    dotProduct
      (c • (Pi.single i (1 : ℝ) : Source48Vector) -
       s • (Pi.single j (1 : ℝ) : Source48Vector))
      (c • (Pi.single i (1 : ℝ) : Source48Vector) -
       s • (Pi.single j (1 : ℝ) : Source48Vector)) = c*c+s*s := by
  classical
  let v : Source48Vector :=
    c • (Pi.single i (1 : ℝ) : Source48Vector) -
    s • (Pi.single j (1 : ℝ) : Source48Vector)
  have hpoint (k : SourceLabel) :
      v k * v k = if k = i then c*c else if k = j then s*s else 0 := by
    by_cases hki : k = i
    · subst k
      simp [v, Pi.single_apply, hij, hij.symm] <;> ring
    · by_cases hkj : k = j
      · subst k
        simp [v, Pi.single_apply, hki] <;> ring
      · simp [v, Pi.single_apply, hki, hkj]
  -- Split the two support points into independent sums.
  -- On L1B Gate #3, simp [Finset.sum_ite] left the singleton
  -- filtered-cardinality goal instead of normalizing the sum.
  have hsplit (k : SourceLabel) :
      (if k = i then c*c else if k = j then s*s else 0) =
      (if k = i then c*c else 0) + (if k = j then s*s else 0) := by
    by_cases hi : k = i
    · have hj : k ≠ j := by
        intro hk
        exact hij (hi.symm.trans hk)
      simp only [if_pos hi, if_neg hj, add_zero]
    · simp only [if_neg hi, zero_add]
  calc
    dotProduct
        (c • (Pi.single i (1 : ℝ) : Source48Vector) -
         s • (Pi.single j (1 : ℝ) : Source48Vector))
        (c • (Pi.single i (1 : ℝ) : Source48Vector) -
         s • (Pi.single j (1 : ℝ) : Source48Vector)) =
        ∑ k : SourceLabel, v k * v k := by
          rfl
    _ = ∑ k : SourceLabel,
          ((if k = i then c*c else 0) +
           (if k = j then s*s else 0)) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hpoint k]
          exact hsplit k
    _ = c*c+s*s := by
          simp [Finset.sum_add_distrib]

/-- Bridge the accepted original `source48Quadratic_eq_dot`
interface to the independent two-coordinate calculation.
No `change` of source48Quadratic or 48-dimensional structure. -/
theorem source48Quadratic_two_coordinate_norm
    (i j : SourceLabel) (hij : i ≠ j) (c s : ℝ) :
    source48Quadratic
      (c • (Pi.single i (1 : ℝ) : Source48Vector) -
       s • (Pi.single j (1 : ℝ) : Source48Vector)) = c*c+s*s := by
  calc
    source48Quadratic
        (c • (Pi.single i (1 : ℝ) : Source48Vector) -
         s • (Pi.single j (1 : ℝ) : Source48Vector)) =
      dotProduct
        (c • (Pi.single i (1 : ℝ) : Source48Vector) -
         s • (Pi.single j (1 : ℝ) : Source48Vector))
        (c • (Pi.single i (1 : ℝ) : Source48Vector) -
         s • (Pi.single j (1 : ℝ) : Source48Vector)) :=
      source48Quadratic_eq_dot _
    _ = c*c+s*s := source48Dot_two_coordinate_norm i j hij c s

#print axioms source48Dot_two_coordinate_norm
#print axioms source48Quadratic_two_coordinate_norm
end
end FCP.BFSSS1V52L1C
