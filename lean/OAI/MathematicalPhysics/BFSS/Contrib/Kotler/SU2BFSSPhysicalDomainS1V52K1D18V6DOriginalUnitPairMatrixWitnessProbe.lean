import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V6COriginalSpinPairMatrixActionAndDetProbe

/-!
K1D18V6D — source-exact witness bridge eliminating the *caller*
typeclass obligations in the accepted V6C original matrix action.

The exact source Q unit premises imply Q a ≠ 0, so the source
normalized polar row and rank-one matrix can be constructed by
derived local invertibility. The matrix is NOT a surrogate source
geometry. Keep the accepted S1V37 matrix and K1D18B polar row.

Statements are candidates pending pinned strict compilation and
independent declaration-level axiom audit. Do not infer generation
of the whole SO48 target, universal Spin factorization, covering,
global Spin9 or BFSS spectral existence.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V6D
noncomputable section
open FCP.BFSSS1V0
open Matrix

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Canonical original rank-one matrix on an original Q-unit source
vector, with source scalar invertibility derived INSIDE this function.
No external typeclass hypothesis or alternate row definition. -/
noncomputable def originalSourceUnitRankOneMatrix
    (u : Source48Vector) (hu : Q u = 1) :
    Matrix Source48Label Source48Label ℝ := by
  have hqu : Q u ≠ 0 := by rw [hu]; exact one_ne_zero
  let : Invertible (Q u) := invertibleOfNonzero hqu
  exact FCP.BFSSS1V37.source48_rankOneConjugationMatrix u
    (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow u)

/-- Accepted V6C original action matrix identity, with ZERO
external invertibility hypotheses. The exact original matrix
representation is packaged in originalSourceUnitRankOneMatrix. -/
theorem originalSourceUnitPairSpin_action_no_instance_premises
    (u v w : Source48Vector) (hu : Q u = 1) (hv : Q v = 1) :
    FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry
      (FCP.BFSSS1V52K1D18V6C.originalSourceUnitPairSpin u v hu hv) w =
    originalSourceUnitRankOneMatrix u hu *ᵥ
      (originalSourceUnitRankOneMatrix v hv *ᵥ w) := by
  have hqu : Q u ≠ 0 := by rw [hu]; exact one_ne_zero
  have hqv : Q v ≠ 0 := by rw [hv]; exact one_ne_zero
  let : Invertible (Q u) := invertibleOfNonzero hqu
  let : Invertible (Q v) := invertibleOfNonzero hqv
  change FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry
      (FCP.BFSSS1V52K1D18V6C.originalSourceUnitPairSpin u v hu hv) w =
    FCP.BFSSS1V37.source48_rankOneConjugationMatrix u
      (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow u) *ᵥ
    (FCP.BFSSS1V37.source48_rankOneConjugationMatrix v
      (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow v) *ᵥ w)
  exact FCP.BFSSS1V52K1D18V6C.originalSourceUnitPairSpin_action
    u v w hu hv

/-- The concrete product of the original source unit-rank-one
matrices has determinant +1 with no caller invertibility assumptions.
This specializes the accepted original K1D18E determinant theorem. -/
theorem originalSourceUnitPairMatrices_det_one
    (u v : Source48Vector) (hu : Q u = 1) (hv : Q v = 1) :
    (originalSourceUnitRankOneMatrix u hu *
      originalSourceUnitRankOneMatrix v hv).det = (1 : ℝ) := by
  have hqu : Q u ≠ 0 := by rw [hu]; exact one_ne_zero
  have hqv : Q v ≠ 0 := by rw [hv]; exact one_ne_zero
  let : Invertible (Q u) := invertibleOfNonzero hqu
  let : Invertible (Q v) := invertibleOfNonzero hqv
  change
    (FCP.BFSSS1V37.source48_rankOneConjugationMatrix u
      (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow u) *
    FCP.BFSSS1V37.source48_rankOneConjugationMatrix v
      (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow v)).det = (1 : ℝ)
  exact FCP.BFSSS1V52K1D18E.originalSourceTwoGeneratorMatrices_det_one u v

#print axioms originalSourceUnitRankOneMatrix
#print axioms originalSourceUnitPairSpin_action_no_instance_premises
#print axioms originalSourceUnitPairMatrices_det_one

end
end FCP.BFSSS1V52K1D18V6D
