import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10EPublicGammaTraceZeroProbe
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
K1D18V10H-F10F — source exact spectral-input gate.

Following accepted F9 determinant magnitude and F10E original
public gamma trace-zero, next prove:
1. exact positive-definiteness of the original nine-vector Q,
   from accepted original Q=dotProduct and PINNED Mathlib
   dotProduct_self_eq_zero;
2. symmetry of every ORIGINAL real gamma linear combination
   from original gamma_symmetric and finite linearity.

These statements are prerequisites for a spectral theorem
and balanced eigenvalue multiplicities. Neither statement
is a determinant-sign theorem. All previous private-table
gamma F10/F10D RED results remain RETAINED and UNQUALIFIED.
No altered original gamma or paired-Fock labels, unproved
Spin9 connectedness, ad-hoc limits or extra axioms.
F10F CANDIDATE only until all three exact types are qualified.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- The EXACT nine-source quadratic form vanishes only
at the zero vector. This is the accepted source Q=dotProduct
plus pinned Mathlib positive definite Euclidean dot-product. -/
theorem source9Quadratic_eq_zero_iff
    (v : SpaceIndex → ℝ) :
    source9Quadratic v = 0 ↔ v = 0 := by
  rw [source9Quadratic_eq_dot]
  exact dotProduct_self_eq_zero

/-- The exact source quadratic form is strictly positive
for each nonzero original nine-vector. -/
theorem source9Quadratic_pos_of_ne
    (v : SpaceIndex → ℝ) (hv : v ≠ 0) :
    0 < source9Quadratic v := by
  have hnonneg : 0 ≤ source9Quadratic v := by
    rw [source9Quadratic_eq_dot]
    change 0 ≤ ∑ i : SpaceIndex, v i * v i
    exact Finset.sum_nonneg (fun i hi => mul_self_nonneg (v i))
  exact lt_of_le_of_ne hnonneg (by
    intro hzero
    exact hv ((source9Quadratic_eq_zero_iff v).mp hzero.symm))

/-- Every ORIGINAL public gamma16 real linear combination
is symmetric. This proof uses no private signed permutation
data and respects the original SpinIndex=Fin16 basis. -/
theorem gammaNineRealLinear_isSymm
    (v : SpaceIndex → ℝ) :
    (gammaNineRealLinear v).IsSymm := by
  change (∑ a : SpaceIndex, (v a) • gamma a)ᵀ =
    ∑ a : SpaceIndex, (v a) • gamma a
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Matrix.transpose_smul, (gamma_symmetric a).eq]

#print axioms source9Quadratic_eq_zero_iff
#print axioms source9Quadratic_pos_of_ne
#print axioms gammaNineRealLinear_isSymm

end
end FCP.BFSSPairedSpin9DetFixture
