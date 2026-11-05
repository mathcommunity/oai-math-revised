import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V37Original48CliffordGeneratorRankOneDeterminantProbe

/-! Owner import from FCP cc608e2282e1b32bb11bbb64424e4775b28138e2,
original source blob 27ed1e4933499c108ee614b4731a3479a318aa8b.
Only imports and this provenance comment are adapted. Definitions, theorem
statements and proof bodies below are source-exact. Local candidate only
until an independent owner strict gate passes. -/

/-!
S1V38 — SOURCE-EXACT 48-real quadratic/dot product and normalized
Clifford-generator coefficient bridge.

Only original FCP.BFSSS1V0.Source48Label = Fin 24 × Fin 2 and
the original source48Quadratic (unit-weight weightedSumSquares).
No surrogate SO representation and no generator-matrix ACTION
identification, Lipschitz hom, Spin determinant+1 or spectral claim.

Five candidate proof roots, unaccepted until strict pinned CI.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000

namespace FCP.BFSSS1V38
noncomputable section

open Matrix
open FCP.BFSSS1V0
open FCP.BFSSS1V37

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Original source Q equals the actual 48-coordinate dot product. -/
theorem source48Quadratic_eq_dot (a : Source48Vector) :
    Q a = a ⬝ᵥ a := by
  simp only [Q, source48Quadratic, QuadraticMap.weightedSumSquares_apply, one_smul]
  rfl

/-- Original source polarization is exactly twice the source dot product. -/
theorem source48_polar_eq_two_dot (a b : Source48Vector) :
    QuadraticMap.polar Q a b = 2 * (a ⬝ᵥ b) := by
  rw [QuadraticMap.polar,
    source48Quadratic_eq_dot (a + b),
    source48Quadratic_eq_dot a, source48Quadratic_eq_dot b]
  simp only [add_dotProduct, dotProduct_add]
  rw [dotProduct_comm b a]
  ring

/-- Canonical ORIGINAL source 48-coordinate coefficient in the
Clifford conjugation formula, not a freely chosen surrogate. -/
noncomputable def source48_normalizedPolarCoeff (a : Source48Vector)
    [Invertible (Q a)] : Source48Vector :=
  (⅟(Q a) * (2 : ℝ)) • a

/-- All-vector coefficient bridge: this true coefficient dot b is
the original Clifford conjugation normalized polar pairing. -/
theorem source48_normalizedPolarCoeff_dot
    (a b : Source48Vector) [Invertible (Q a)] :
    source48_normalizedPolarCoeff a ⬝ᵥ b =
      ⅟(Q a) * QuadraticMap.polar Q a b := by
  change ((⅟(Q a) * (2 : ℝ)) • a) ⬝ᵥ b =
    ⅟(Q a) * QuadraticMap.polar Q a b
  rw [smul_dotProduct, source48_polar_eq_two_dot]
  simp only [smul_eq_mul]
  ring

/-- The exact normalized source coefficient evaluates to 2 on a. -/
theorem source48_normalizedPolarCoeff_dot_self
    (a : Source48Vector) [Invertible (Q a)] :
    source48_normalizedPolarCoeff a ⬝ᵥ a = (2 : ℝ) := by
  rw [source48_normalizedPolarCoeff_dot]
  exact FCP.BFSSS1V37.source48_polar_inverse_self a

/-- The formerly conditional S1V37 rank-one determinant is now -1
for the ACTUAL source-Q normalized coefficient, not an arbitrary ell.
This is not yet an identification of the matrix with a unit action. -/
theorem source48_originalNormalizedRankOne_det
    (a : Source48Vector) [Invertible (Q a)] :
    (FCP.BFSSS1V37.source48_rankOneConjugationMatrix
      a (source48_normalizedPolarCoeff a)).det = (-1 : ℝ) := by
  exact FCP.BFSSS1V37.source48_rankOneConjugationMatrix_det
    a (source48_normalizedPolarCoeff a)
    (source48_normalizedPolarCoeff_dot_self a)

#print axioms source48Quadratic_eq_dot
#print axioms source48_polar_eq_two_dot
#print axioms source48_normalizedPolarCoeff_dot
#print axioms source48_normalizedPolarCoeff_dot_self
#print axioms source48_originalNormalizedRankOne_det

end
end FCP.BFSSS1V38
