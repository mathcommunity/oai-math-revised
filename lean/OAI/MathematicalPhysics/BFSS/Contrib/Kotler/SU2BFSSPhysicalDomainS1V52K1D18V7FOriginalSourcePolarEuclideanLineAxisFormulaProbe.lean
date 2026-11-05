import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7EOriginalSourceSOEuclideanDeterminantTransportProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V6DOriginalUnitPairMatrixWitnessProbe
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
K1D18V7F — exact original source-Q polarization and Euclidean line-axis formula.

No new source Q, source 48-label ordering or Clifford vector action.
The accepted V7B/V7C source-Q norm-square identity is converted to
a polar/inner-product identity by a GENERIC real inner-product lemma.
The accepted V6D actual original rank-one matrix action and K1D18B/C
source polar row are then matched to the same 48-label Euclidean
line-axis formula. Its negative is the corresponding hyperplane
reflection formula.

This does NOT yet prove equality with Mathlib Submodule.reflection,
unconditional Spin image surjectivity, covering, global Spin9 or
BFSS spectral existence. Candidate until independent strict CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7F
noncomputable section
open FCP.BFSSS1V0
open Matrix

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev Euc48 := EuclideanSpace ℝ Source48Label
private abbrev E : Source48Vector ≃ₗ[ℝ] Euc48 :=
  FCP.BFSSS1V52K1D18V7C.originalSource48ToEuclidean

/-- Generic polarization identity, stated independently of the
original 48-coordinate expression and its reducible Q definition. -/
theorem quadraticPolar_eq_two_realInner_of_normSq
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (q : QuadraticForm ℝ V) (e : V ≃ₗ[ℝ] W)
    (hsq : ∀ x : V, q x = ‖e x‖ ^ 2) (x y : V) :
    QuadraticMap.polar q x y = 2 * inner ℝ (e x) (e y) := by
  rw [QuadraticMap.polar, hsq (x + y), hsq x, hsq y,
      map_add, norm_add_sq_real]
  ring

/-- The ACTUAL original source Q polar form is twice the inner
product of the SAME 48-label coordinates in EuclideanSpace. -/
theorem originalSourcePolar_eq_twoEuclideanInner
    (u w : Source48Vector) :
    QuadraticMap.polar Q u w = 2 * inner ℝ (E u) (E w) := by
  apply quadraticPolar_eq_two_realInner_of_normSq Q E
  intro x
  exact (FCP.BFSSS1V52K1D18V7C.originalSource48ToEuclidean_norm_sq_eq_Q x).symm

/-- A Q-unit ORIGINAL source vector maps to a unit Euclidean vector.
This is a consequence of accepted source-Q equality and positivity. -/
theorem originalSourceUnitQ_euclidean_norm_one
    (u : Source48Vector) (hu : Q u = 1) :
    ‖E u‖ = 1 := by
  have hsq : ‖E u‖ ^ 2 = 1 := by
    rw [FCP.BFSSS1V52K1D18V7C.originalSource48ToEuclidean_norm_sq_eq_Q, hu]
  nlinarith [norm_nonneg (E u)]

/-- The ACTUAL original source S1V37 rank-one Clifford matrix, with
the V6D derived unit-Q instance, acts in Euclidean coordinates as
2 inner(u,w) times u minus w. This is an EXACT source-action bridge,
not a surrogate formula substituted for the original matrix. -/
theorem originalSourceUnitRankOne_euclidean_action
    (u w : Source48Vector) (hu : Q u = 1) :
    E (FCP.BFSSS1V52K1D18V6D.originalSourceUnitRankOneMatrix u hu *ᵥ w) =
      (2 * inner ℝ (E u) (E w)) • E u - E w := by
  have hqu : Q u ≠ 0 := by rw [hu]; exact one_ne_zero
  let : Invertible (Q u) := invertibleOfNonzero hqu
  have hinv : ⅟(Q u) = (1 : ℝ) := by
    calc
      ⅟(Q u) = ⅟(Q u) * Q u := by simp only [hu, mul_one]
      _ = 1 := invOf_mul_self (Q u)
  change E (FCP.BFSSS1V37.source48_rankOneConjugationMatrix u
    (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow u) *ᵥ w) = _
  rw [FCP.BFSSS1V52K1D18C.source48_rankOneConjugationMatrix_mulVec,
      FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow_dot,
      hinv, one_mul, map_sub, map_smul,
      originalSourcePolar_eq_twoEuclideanInner]

/-- The same ORIGINAL source Clifford line-axis action is minus the
Euclidean hyperplane-reflection scalar formula; matching the
corresponding Mathlib reflection map is a separate next theorem. -/
theorem originalSourceUnitRankOne_eq_negative_euclideanHyperplaneFormula
    (u w : Source48Vector) (hu : Q u = 1) :
    E (FCP.BFSSS1V52K1D18V6D.originalSourceUnitRankOneMatrix u hu *ᵥ w) =
      -(E w - (2 * inner ℝ (E u) (E w)) • E u) := by
  rw [originalSourceUnitRankOne_euclidean_action u w hu]
  abel

#print axioms quadraticPolar_eq_two_realInner_of_normSq
#print axioms originalSourcePolar_eq_twoEuclideanInner
#print axioms originalSourceUnitQ_euclidean_norm_one
#print axioms originalSourceUnitRankOne_euclidean_action
#print axioms originalSourceUnitRankOne_eq_negative_euclideanHyperplaneFormula

end
end FCP.BFSSS1V52K1D18V7F
