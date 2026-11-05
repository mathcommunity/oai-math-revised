import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5GOriginalSU2QuarticJacobiProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5HSourceCenteredGammaGramProbe

/-!
L6G5I: exact source quadratic coefficient is a real scalar (cast to C),
and the accepted centered gamma matrix has the required spinor-row Gram.

These are two source-faithful small lemmas toward the original
quartic potential identity. They do not assume any color contraction,
nor do they assert source quadratic square = bosonic potential yet.
-/
set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G5I
noncomputable section
open scoped Matrix BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G1
open FCP.BFSSSU2PhysicalDomainL6G2
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G4A
open FCP.BFSSSU2PhysicalDomainL6G4B
open FCP.BFSSSU2PhysicalDomainL6G5F
open FCP.BFSSSU2PhysicalDomainL6G5H

/-- Exact coefficient before canonical Real-to-Complex inclusion. -/
def sourceQuadraticPointReal {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ)
    (p : FermionLabel N) (x : Boson N) : ℝ :=
  ∑ α : SpinIndex, w α *
    (∑ v : BosonLabel N, ∑ t : BosonLabel N,
      ((1 / 2 : ℝ) * M.structureConstant p.2 v.2 t.2 *
        M.gammaTwo v.1 t.1 α p.1) * x v * x t)

/-- The L6G5F original complex point coefficient contains no hidden
imaginary part. No Pauli-color or gamma-matching premise is used. -/
theorem sourceQuadraticPointCoefficient_eq_real {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ)
    (p : FermionLabel N) (x : Boson N) :
    sourceQuadraticPointCoefficient M w p x =
      (sourceQuadraticPointReal M w p x : ℂ) := by
  unfold sourceQuadraticPointCoefficient sourceQuadraticPointReal
    sourceQuadraticWeight
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]

/-- A fixed real row of the L6G5H original centered gamma matrix.
This is exactly the matrix input to the color-specific source spinor
coefficient, not a new representation or operator. -/
theorem sourceCenteredGammaPair_rowGram {N : ℕ}
    (M : AlgebraData N) (u v : SpaceIndex → ℝ)
    (w : SpinIndex → ℝ) :
    (∑ β : SpinIndex,
      ((w ᵥ* sourceCenteredGammaPair M u v) β) ^ 2) =
      (((∑ i : SpaceIndex, u i ^ 2) *
        (∑ i : SpaceIndex, v i ^ 2)) -
        (∑ i : SpaceIndex, u i * v i) ^ 2) *
          spinorSquareNorm w := by
  let C := sourceCenteredGammaPair M u v
  have hrow : w ᵥ* C = C.transpose *ᵥ w := by
    ext β
    change (∑ α, w α * C α β) = ∑ α, C α β * w α
    apply Finset.sum_congr rfl
    intro α _
    ring
  change (∑ β : SpinIndex, ((w ᵥ* C) β) ^ 2) = _
  rw [hrow]
  have hdot :
      (∑ β : SpinIndex, ((C.transpose *ᵥ w) β) ^ 2) =
        dotProduct (C.transpose *ᵥ w) (C.transpose *ᵥ w) := by
    simp only [dotProduct, pow_two]
  rw [hdot]
  rw [OAI.BFSSGamma.dot_mulVec_left, Matrix.transpose_transpose,
    Matrix.mulVec_mulVec]
  rw [show C * C.transpose =
    (((∑ i : SpaceIndex, u i ^ 2) *
      (∑ i : SpaceIndex, v i ^ 2)) -
      (∑ i : SpaceIndex, u i * v i) ^ 2) • (1 : GammaMatrix) from
      sourceCenteredGammaPair_gram M u v]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct,
    Pi.smul_apply, smul_eq_mul]
  unfold spinorSquareNorm
  simp only [pow_two]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  ring

#print axioms sourceQuadraticPointCoefficient_eq_real
#print axioms sourceCenteredGammaPair_rowGram
#check @sourceQuadraticPointCoefficient_eq_real
#check @sourceCenteredGammaPair_rowGram
end
end FCP.BFSSSU2PhysicalDomainL6G5I
