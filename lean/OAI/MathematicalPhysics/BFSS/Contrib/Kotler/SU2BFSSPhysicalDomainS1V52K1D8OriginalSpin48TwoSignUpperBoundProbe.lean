import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D7OriginalCliffordScalarCoefficientNormProbe

/-!
K1D8 — original Spin(48) trivial-vector-action kernel TWO-SIGN UPPER BOUND.

Accepted K1D7 supplies an exact real coefficient c, the genuine
original-source Clifford equality, and c*c=1 in the real field.
Factor c*c - 1 and use the no-zero-divisors property of the reals.
No guesswork about Clifford bases or equivExterior multiplicativity.

The result only shows kernel ELEMENTS are represented by ±1 in the
original Clifford algebra. It does NOT assert the negative Clifford
unit is an element of the actual Mathlib spinGroup subtype or that
the vector action kernel contains both signs. CANDIDATE pending strict CI.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52K1D8
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- For a genuine original Spin48 vector-action kernel element,
the exact real coefficient of its scalar Clifford representative
must be +1 or -1; existence alone does not classify Spin membership. -/
theorem originalSourceSpin48_trivialAction_scalar_coefficient_two_signs
    (s : spinGroup Q)
    (hs : ∀ v : Source48Vector,
      FCP.BFSSS1V31.sourceSpin48VectorAction s v = v) :
    ∃ c : ℝ, (s : C) = algebraMap ℝ C c ∧ (c = 1 ∨ c = -1) := by
  obtain ⟨c, hc, hsq⟩ :=
    FCP.BFSSS1V52K1D7.originalSourceSpin48_trivialAction_clifford_scalar_coefficient_square_one
      s hs
  have hfactor : (c - 1) * (c + 1) = 0 := by
    calc
      (c - 1) * (c + 1) = c * c - 1 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · exact ⟨c, hc, Or.inl (sub_eq_zero.mp hminus)⟩
  · have hneg : c = -1 := by linarith
    exact ⟨c, hc, Or.inr hneg⟩

/-- Upper bound in the original Clifford algebra: source-trivial
Spin48 elements have Clifford value either 1 or -1. No claim that
negative one belongs to spinGroup is hidden in this disjunction. -/
theorem originalSourceSpin48_trivialAction_clifford_one_or_neg_one
    (s : spinGroup Q)
    (hs : ∀ v : Source48Vector,
      FCP.BFSSS1V31.sourceSpin48VectorAction s v = v) :
    (s : C) = 1 ∨ (s : C) = -1 := by
  obtain ⟨c, hc, hsign⟩ :=
    originalSourceSpin48_trivialAction_scalar_coefficient_two_signs s hs
  rcases hsign with hone | hneg
  · left
    simpa [hone] using hc
  · right
    simpa [hneg] using hc

#print axioms originalSourceSpin48_trivialAction_scalar_coefficient_two_signs
#print axioms originalSourceSpin48_trivialAction_clifford_one_or_neg_one

end
end FCP.BFSSS1V52K1D8
