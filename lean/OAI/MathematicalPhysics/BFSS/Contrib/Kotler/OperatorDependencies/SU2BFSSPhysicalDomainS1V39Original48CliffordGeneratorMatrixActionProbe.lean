import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V38Original48PolarCoefficientBridgeProbe

/-!
S1V39 — exact original 48-real rank-one matrix action and source
Clifford degree-one conjugation bridge.

All operators use original Fin 24 × Fin 2 coordinates and original
unit-weight source48Quadratic. No surrogate representation is introduced.

Only after strict compilation can any of these roots be accepted.
This does NOT construct the Lipschitz group action, full Spin
orientation, covering, global SU(2) lift or manuscript/spectral bridge.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000

namespace FCP.BFSSS1V39
noncomputable section

open Matrix
open FCP.BFSSS1V0
open FCP.BFSSS1V37
open FCP.BFSSS1V38

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- The source 48-by-1 column times the genuine 1-by-48 row acts by
the original dot pairing. This explicit typed interface prevents
the earlier S1V37 untyped rewrite-matching failures. -/
theorem source48_rankOne_mulVec
    (a ell b : Source48Vector) :
    Matrix.replicateCol (Fin 1) a *ᵥ
        (Matrix.replicateRow (Fin 1) (-ell) *ᵥ b) =
      ((-ell) ⬝ᵥ b) • a := by
  have hrow :
      Matrix.replicateRow (Fin 1) (-ell) *ᵥ b =
        (fun _ : Fin 1 => (-ell) ⬝ᵥ b) := by
    exact Matrix.replicateRow_mulVec_eq_const (ι := Fin 1) (-ell) b
  rw [hrow]
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.replicateCol_apply,
    Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul]
  ring

/-- On EVERY original 48-real source vector, the exact S1V37
rank-one matrix acts as ell(a,b) a - b. -/
theorem source48_rankOneConjugationMatrix_mulVec
    (a ell b : Source48Vector) :
    FCP.BFSSS1V37.source48_rankOneConjugationMatrix a ell *ᵥ b =
      (ell ⬝ᵥ b) • a - b := by
  have hmat :
      FCP.BFSSS1V37.source48_rankOneConjugationMatrix a ell *ᵥ b =
        -(b + ((-ell) ⬝ᵥ b) • a) := by
    unfold FCP.BFSSS1V37.source48_rankOneConjugationMatrix
    rw [Matrix.neg_mulVec, Matrix.add_mulVec,
      Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      source48_rankOne_mulVec]
  calc
    FCP.BFSSS1V37.source48_rankOneConjugationMatrix a ell *ᵥ b =
        -(b + ((-ell) ⬝ᵥ b) • a) := hmat
    _ = (ell ⬝ᵥ b) • a - b := by
      rw [neg_dotProduct]
      simp only [neg_smul]
      abel

/-- The actual original source-Q normalized coefficient now
specializes the all-vector matrix-action lemma to the exact
Clifford conjugation input vector. -/
theorem source48_originalGeneratorMatrix_mulVec
    (a b : Source48Vector) [Invertible (Q a)] :
    FCP.BFSSS1V37.source48_rankOneConjugationMatrix
        a (FCP.BFSSS1V38.source48_normalizedPolarCoeff a) *ᵥ b =
      (⅟(Q a) * QuadraticMap.polar Q a b) • a - b := by
  rw [source48_rankOneConjugationMatrix_mulVec,
    FCP.BFSSS1V38.source48_normalizedPolarCoeff_dot]

/-- The original source 48-real matrix and genuine invertible
Clifford ι(Q,a) give literally identical conjugated Clifford vectors.
No abstract Pin or topological lift is inserted. -/
theorem source48_originalGeneratorMatrix_cliffordConjugation
    (a b : Source48Vector)
    [Invertible (Q a)] [Invertible (CliffordAlgebra.ι Q a)] :
    CliffordAlgebra.ι Q
      (FCP.BFSSS1V37.source48_rankOneConjugationMatrix
         a (FCP.BFSSS1V38.source48_normalizedPolarCoeff a) *ᵥ b) =
      CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b *
        ⅟(CliffordAlgebra.ι Q a) := by
  rw [source48_originalGeneratorMatrix_mulVec]
  exact FCP.BFSSS1V37.source48_clifford_generator_conjugation a b

#print axioms source48_rankOne_mulVec
#print axioms source48_rankOneConjugationMatrix_mulVec
#print axioms source48_originalGeneratorMatrix_mulVec
#print axioms source48_originalGeneratorMatrix_cliffordConjugation

end
end FCP.BFSSS1V39
