import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18BPolarAllVectorCliffordBridgeProbe
import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
K1D18C: exact original rank-one matrix implementation of genuine source
Clifford degree-one generator conjugation, with determinant -1.

The source matrix is the original S1V37 definition. The polar row is
the accepted source K1D18B definition. No alternative matrix, source
ordering, representation, quadratic form or group action is inserted.

The determinant of EVERY actual source spinGroup element, the full
Lipschitz closure/parity theorem, global Spin9, covering and spectra
remain separately unproved. Candidate until strict owner CI evidence.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18C
noncomputable section

open FCP.BFSSS1V0
open Matrix

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- The exact original 48-by-48 rank-one matrix computes the source
normalized polar contraction minus the original vector. -/
theorem source48_rankOneConjugationMatrix_mulVec
    (a ell b : Source48Vector) :
    FCP.BFSSS1V37.source48_rankOneConjugationMatrix a ell *ᵥ b =
      (ell ⬝ᵥ b) • a - b := by
  have hprod :
      (Matrix.replicateCol (Fin 1) a * Matrix.replicateRow (Fin 1) (-ell)) *ᵥ b =
        (MulOpposite.op ((-ell) ⬝ᵥ b)) • a := by
    have hmatrix :
        Matrix.replicateCol (Fin 1) a * Matrix.replicateRow (Fin 1) (-ell) =
          Matrix.vecMulVec a (-ell) := by
      exact (Matrix.vecMulVec_eq (ι := Fin 1) a (-ell)).symm
    rw [hmatrix]
    exact Matrix.vecMulVec_mulVec a (-ell) b
  have hscalar :
      (MulOpposite.op ((-ell) ⬝ᵥ b)) • a =
        -((ell ⬝ᵥ b) • a) := by
    ext j
    change a j * ((-ell) ⬝ᵥ b) = -((ell ⬝ᵥ b) * a j)
    rw [neg_dotProduct]
    ring
  calc
    FCP.BFSSS1V37.source48_rankOneConjugationMatrix a ell *ᵥ b =
        -(b + (Matrix.replicateCol (Fin 1) a *
          Matrix.replicateRow (Fin 1) (-ell)) *ᵥ b) := by
            simp only [FCP.BFSSS1V37.source48_rankOneConjugationMatrix,
              Matrix.neg_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
    _ = -(b + (MulOpposite.op ((-ell) ⬝ᵥ b)) • a) := by rw [hprod]
    _ = (ell ⬝ᵥ b) • a - b := by
          rw [hscalar]
          abel

/-- The ACTUAL source degree-one Clifford conjugation is the rank-one
matrix action on the original Fin24 × Fin2 source vector, not merely
a determinant calculation for an unrelated matrix. -/
theorem source48_rankOneMatrix_matches_original_clifford_conjugation
    (a b : Source48Vector)
    [Invertible (CliffordAlgebra.ι Q a)] [Invertible (Q a)] :
    CliffordAlgebra.ι Q
      (FCP.BFSSS1V37.source48_rankOneConjugationMatrix a
        (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a) *ᵥ b) =
        CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b *
          ⅟(CliffordAlgebra.ι Q a) := by
  rw [source48_rankOneConjugationMatrix_mulVec]
  exact FCP.BFSSS1V52K1D18B.source48_clifford_generator_conjugation_from_row a b

/-- A single genuine invertible original Clifford generator acts
through the exact source rank-one matrix of determinant -1; the
Spin48 even-parity closure remains a separate theorem. -/
theorem source48_original_generator_rankOneMatrix_det
    (a : Source48Vector) [Invertible (Q a)] :
    (FCP.BFSSS1V37.source48_rankOneConjugationMatrix a
      (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a)).det = (-1 : ℝ) := by
  exact FCP.BFSSS1V37.source48_rankOneConjugationMatrix_det
    a (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a)
    (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow_dot_self a)

#print axioms source48_rankOneConjugationMatrix_mulVec
#print axioms source48_rankOneMatrix_matches_original_clifford_conjugation
#print axioms source48_original_generator_rankOneMatrix_det

end
end FCP.BFSSS1V52K1D18C
