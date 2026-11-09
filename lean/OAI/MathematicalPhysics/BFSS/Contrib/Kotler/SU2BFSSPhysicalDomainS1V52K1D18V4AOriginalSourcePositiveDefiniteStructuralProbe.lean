import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V3OriginalSourceRankOneQuadraticIsometryProbe

/-!
K1D18V4A — a DIFFERENT positivity architecture after three original
V4 sum-of-squares conversion failures: prove PosDef directly on a
generic weighted sum of one-valued squares, then specialize ONLY
the resulting predicate to the exact original source Q.

This intentionally does not import the failed V4 module or prove the
concrete sum-of-48-squares normal form. Original source S1V0
Source48Label/Source48Vector/source48Quadratic remain unchanged.
All three statements are CANDIDATES pending strict compilation
and independent declaration-level axiom audit.

No normalized source unit vector, Clifford star/Pin factorization,
Spin lift, SO48 surjectivity, covering, or BFSS physical conclusion.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V4A
noncomputable section
open FCP.BFSSS1V0

/-- Source-independent structure: a finite all-one real weighted
quadratic sum of squares is positive definite. No concrete 48-index
sum expression appears in the source specialization. -/
theorem weightedSumSquares_one_posDef
    {ι : Type*} [Fintype ι] :
    (QuadraticMap.weightedSumSquares ℝ
      (fun _ : ι => (1 : ℝ))).PosDef := by
  intro a ha
  rw [QuadraticMap.weightedSumSquares_apply]
  simp only [one_smul]
  apply Finset.sum_pos'
  · intro j _
    exact mul_self_nonneg (a j)
  · obtain ⟨j, hj⟩ : ∃ j : ι, a j ≠ 0 := by
      by_contra h
      apply ha
      funext j
      by_contra hj
      exact h ⟨j, hj⟩
    exact ⟨j, Finset.mem_univ j, (mul_self_pos).2 hj⟩

/-- The EXISTING original 48-real source Q itself is positive
definite. This is a bridge to the source definition, not a replacement
Euclidean quadratic form. -/
theorem source48Quadratic_posDef :
    source48Quadratic.PosDef := by
  exact weightedSumSquares_one_posDef (ι := Source48Label)

/-- Original nonzero source vectors have positive original quadratic
value; no separate coordinate sum or finite-label expansion needed. -/
theorem source48Quadratic_pos_of_ne_zero (a : Source48Vector)
    (ha : a ≠ 0) : 0 < source48Quadratic a := by
  exact source48Quadratic_posDef a ha

#print axioms weightedSumSquares_one_posDef
#print axioms source48Quadratic_posDef
#print axioms source48Quadratic_pos_of_ne_zero

end
end FCP.BFSSS1V52K1D18V4A
