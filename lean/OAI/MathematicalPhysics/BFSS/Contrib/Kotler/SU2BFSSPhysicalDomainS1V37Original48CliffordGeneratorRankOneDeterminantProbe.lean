import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V0StandaloneOrthogonalGeometryProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Owner import from FCP cc608e2282e1b32bb11bbb64424e4775b28138e2,
original source blob 2d3d40134e4eaba80751c62a160d1803f22c828b.
Only imports and this provenance comment are adapted. Definitions, theorem
statements and proof bodies below are source-exact. Local candidate only
until an independent owner strict gate passes. -/

/-!
S1V37 — SOURCE-SIZED determinant of one genuine invertible Clifford generator.
Candidate only until strict source-pinned Lean compilation and axiom audit.

Three separately scoped obligations:
1. Exact source-Q polar self-identity divided by invertible Q(a).
2. The true pinned Clifford conjugation formula for an invertible degree-one
   source generator, with NO replacement of original source vectors.
3. Rank-one 48-real matrix determinant -1, given only the exact normalization
   ell(a) = 2. No guessed Spin orientation or Lipschitz extension is claimed.

The bridge identifying the matrix with the original Clifford vector action
for arbitrary generators, and the later full Lipschitz parity/Spin orientation,
are NOT yet proved by this module.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000

namespace FCP.BFSSS1V37
noncomputable section

open Matrix
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Real polarization on the ACTUAL source 48-vector and its invertible
quadratic norm: the normalized polar pairing of a vector with itself is 2. -/
theorem source48_polar_inverse_self
    (a : Source48Vector) [Invertible (Q a)] :
    ⅟(Q a) * QuadraticMap.polar Q a a = (2 : ℝ) := by
  rw [QuadraticMap.polar_self, two_smul, mul_add]
  rw [invOf_mul_self]
  norm_num

/-- Actual original source Clifford degree-one conjugation, not an abstract
action or a presumed matrix-to-Clifford source identification. -/
theorem source48_clifford_generator_conjugation
    (a b : Source48Vector)
    [Invertible (CliffordAlgebra.ι Q a)] [Invertible (Q a)] :
    CliffordAlgebra.ι Q
      ((⅟(Q a) * QuadraticMap.polar Q a b) • a - b) =
      CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b *
        ⅟(CliffordAlgebra.ι Q a) := by
  exact (CliffordAlgebra.ι_mul_ι_mul_invOf_ι Q a b).symm

/-- Matrix of -(I - a ellᵀ), on EXACTLY the original Fin24 × Fin2
source 48-real coordinates. Parameter ell is an arbitrary coefficient vector;
its identification with normalized source polarization is still a separate
proof obligation. -/
noncomputable def source48_rankOneConjugationMatrix
    (a ell : Source48Vector) : Matrix Source48Label Source48Label ℝ :=
  -(1 + Matrix.replicateCol (Fin 1) a *
         Matrix.replicateRow (Fin 1) (-ell))

/-- Determinant -1 from ell dot a = 2, in true original dimension 48.
This is a source-size linear-algebra lemma, not yet the entire Lipschitz
generator determinant theorem: the source coefficient bridge is separate. -/
theorem source48_rankOneConjugationMatrix_det
    (a ell : Source48Vector)
    (h : ell ⬝ᵥ a = (2 : ℝ)) :
    (source48_rankOneConjugationMatrix a ell).det = (-1 : ℝ) := by
  unfold source48_rankOneConjugationMatrix
  have hmatrix :
      (1 + Matrix.replicateCol (Fin 1) a *
        Matrix.replicateRow (Fin 1) (-ell)).det =
        1 + (-ell) ⬝ᵥ a := by
    exact Matrix.det_one_add_replicateCol_mul_replicateRow
      (ι := Fin 1) a (-ell)
  calc
    (-(1 + Matrix.replicateCol (Fin 1) a *
      Matrix.replicateRow (Fin 1) (-ell))).det =
        (-1 : ℝ) ^ Fintype.card Source48Label *
          (1 + Matrix.replicateCol (Fin 1) a *
            Matrix.replicateRow (Fin 1) (-ell)).det := Matrix.det_neg _
    _ = (-1 : ℝ) ^ Fintype.card Source48Label *
          (1 + (-ell) ⬝ᵥ a) := by rw [hmatrix]
    _ = -1 := by
      rw [neg_dotProduct, h]
      norm_num [Source48Label, Fintype.card_prod]

#print axioms source48_polar_inverse_self
#print axioms source48_clifford_generator_conjugation
#print axioms source48_rankOneConjugationMatrix_det

end
end FCP.BFSSS1V37
