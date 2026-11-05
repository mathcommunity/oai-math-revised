import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9ContinuousMonoidOrthogonalFlowProbe
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Connected.PathConnected

/-!
K1D18V10A — determinant-one and special-orthogonal membership
for each original 48-label paired-Fock real skew-matrix exponential.

Pinned Mathlib's MatrixExponential.lean leaves the full formula
det(exp A) = exp(trace A) as a TODO. We therefore use the
existing source-exact V9V orthogonality, V9Y continuity, V9W
identity at zero, and pinned IsPreconnected.eq_of_sq_eq.

This is an actual SO(48) orientation result for each fixed-generator
flow. It is NOT a global Spin(9) group integration, topological
Spin(48) covering, source CAR implementation, or BFSS physical theorem.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open NormedSpace

/-- Every original paired-label real skew matrix has a
determinant-one exponential at every real time. No imported
det(exp A) formula is assumed. -/
theorem pairedSkewExp_det_one
    (X : Matrix Source48Label Source48Label ℝ)
    (hX : X.transpose = -X) (t : ℝ) :
    (exp (t • X)).det = 1 := by
  let f : ℝ → ℝ := fun u => (exp (u • X)).det
  have hf : Continuous f :=
    (pairedMatrixExp_continuous_real X).matrix_det
  have hsq : Set.EqOn (f ^ 2)
      ((fun _ : ℝ => (1 : ℝ)) ^ 2) Set.univ := by
    intro u _
    change (exp (u • X)).det ^ 2 = (1 : ℝ) ^ 2
    have horth :
        exp (u • X) * (exp (u • X)).transpose =
          (1 : Matrix Source48Label Source48Label ℝ) := by
      have hm := pairedSkewExp_mem_orthogonalGroup X hX u
      rw [Matrix.mem_orthogonalGroup_iff] at hm
      exact hm
    have hdet := congrArg Matrix.det horth
    simpa only [Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_one, pow_two, one_mul] using hdet
  have hzero : f 0 = 1 := by
    change (exp ((0 : ℝ) • X)).det = 1
    rw [pairedMatrixExp_zero X]
    exact Matrix.det_one
  have hglobal : Set.EqOn f (fun _ : ℝ => (1 : ℝ)) Set.univ :=
    (isPreconnected_univ (α := ℝ)).eq_of_sq_eq
      hf.continuousOn continuousOn_const hsq
      (by intro _ _; exact one_ne_zero)
      (Set.mem_univ (0 : ℝ)) hzero
  exact hglobal (Set.mem_univ t)

/-- The same original paired-Fock exponentials are members
of the genuine pinned Matrix.specialOrthogonalGroup subtype. -/
theorem pairedSkewExp_mem_specialOrthogonalGroup
    (X : Matrix Source48Label Source48Label ℝ)
    (hX : X.transpose = -X) (t : ℝ) :
    exp (t • X) ∈
      Matrix.specialOrthogonalGroup Source48Label ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  exact ⟨pairedSkewExp_mem_orthogonalGroup X hX t,
    pairedSkewExp_det_one X hX t⟩

#print axioms pairedSkewExp_det_one
#print axioms pairedSkewExp_mem_specialOrthogonalGroup

end
end FCP.BFSSPairedSpin9Plane
