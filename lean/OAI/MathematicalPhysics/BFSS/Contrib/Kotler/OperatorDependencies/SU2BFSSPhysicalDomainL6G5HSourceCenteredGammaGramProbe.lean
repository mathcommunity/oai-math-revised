import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5FSourceQuarticPointwiseProbe
import OAI.MathematicalPhysics.BFSS.CliffordSymbols
import Mathlib.Tactic.Module

/-!
L6G5H — centered Clifford-pair Gram for the EXACT pinned gammaLinear.

For U=sum_i u_i gamma_i, V=sum_i v_i gamma_i, d=sum_i u_i v_i,
define C=UV-d I. Because U and V are real symmetric, C^T=VU-dI.
The upstream genuine Clifford mixed/square theorems imply
C*C^T=(||u||² ||v||²-d²) I.

No replacement gamma, source theta, color or physical model is assumed.
The color bracket / pointwise coefficient transport remains separate.
-/

set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G5H
noncomputable section
open scoped Matrix BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData

/-- Scalar-central Gram product of two noncommuting elements. Both
orders AB and BA are retained. This is ring theory, not a gamma axiom. -/
private theorem centeredProduct_gram
    {R : Type*} [Ring R] [Algebra ℝ R]
    (A B : R) (a b d : ℝ)
    (hAA : A * A = a • (1 : R))
    (hBB : B * B = b • (1 : R))
    (hAB : A * B + B * A = (2 * d) • (1 : R)) :
    (A * B - d • (1 : R)) * (B * A - d • (1 : R)) =
      (a * b - d * d) • (1 : R) := by
  have habba : (A * B) * (B * A) = (a * b) • (1 : R) := by
    calc
      _ = A * (B * B) * A := by noncomm_ring
      _ = A * (b • (1 : R)) * A := by rw [hBB]
      _ = b • (A * A) := by
        simp only [mul_smul_comm, smul_mul_assoc, mul_one]
      _ = b • (a • (1 : R)) := by rw [hAA]
      _ = _ := by rw [smul_smul, mul_comm b a]
  have hright (T : R) : T * (d • (1 : R)) = d • T := by
    rw [mul_smul_comm, mul_one]
  have hleft (T : R) : (d • (1 : R)) * T = d • T := by
    rw [smul_mul_assoc, one_mul]
  have hd2 :
      (d • (1 : R)) * (d • (1 : R)) = (d * d) • (1 : R) := by
    rw [hleft (d • (1 : R)), smul_smul]
  have hexpand :
      (A * B - d • (1 : R)) * (B * A - d • (1 : R)) =
        (A * B) * (B * A) -
          d • (A * B + B * A) + (d * d) • (1 : R) := by
    simp only [mul_sub, sub_mul, hright, hleft, smul_add]
    module
  calc
    _ = (A * B) * (B * A) -
          d • (A * B + B * A) + (d * d) • (1 : R) := hexpand
    _ = (a * b) • (1 : R) -
          d • ((2 * d) • (1 : R)) + (d * d) • (1 : R) := by
            rw [habba, hAB]
    _ = _ := by
      rw [smul_smul, ← sub_smul, ← add_smul]
      congr 1
      ring

/-- Centering the genuine Clifford product, source matrix type. -/
def sourceCenteredGammaPair {N : ℕ}
    (M : AlgebraData N) (u v : SpaceIndex → ℝ) : GammaMatrix :=
  M.gammaLinear u * M.gammaLinear v -
    (∑ i : SpaceIndex, u i * v i) • (1 : GammaMatrix)

theorem sourceCenteredGammaPair_transpose {N : ℕ}
    (M : AlgebraData N) (u v : SpaceIndex → ℝ) :
    (sourceCenteredGammaPair M u v).transpose =
      M.gammaLinear v * M.gammaLinear u -
        (∑ i : SpaceIndex, u i * v i) • (1 : GammaMatrix) := by
  unfold sourceCenteredGammaPair
  simp only [Matrix.transpose_sub, Matrix.transpose_mul,
    Matrix.transpose_smul, Matrix.transpose_one,
    (M.gammaLinear_symmetric u).eq,
    (M.gammaLinear_symmetric v).eq]

/-- The crucial real spinor Gram matrix, under exactly upstream
AlgebraData Clifford and symmetry fields, not new hypotheses. -/
theorem sourceCenteredGammaPair_gram {N : ℕ}
    (M : AlgebraData N) (u v : SpaceIndex → ℝ) :
    sourceCenteredGammaPair M u v *
      (sourceCenteredGammaPair M u v).transpose =
      (((∑ i : SpaceIndex, u i ^ 2) *
          (∑ i : SpaceIndex, v i ^ 2)) -
        (∑ i : SpaceIndex, u i * v i) ^ 2) •
          (1 : GammaMatrix) := by
  rw [sourceCenteredGammaPair_transpose]
  unfold sourceCenteredGammaPair
  have h := centeredProduct_gram
    (M.gammaLinear u) (M.gammaLinear v)
    (∑ i : SpaceIndex, u i ^ 2)
    (∑ i : SpaceIndex, v i ^ 2)
    (∑ i : SpaceIndex, u i * v i)
    (M.gammaLinear_sq u) (M.gammaLinear_sq v)
    (M.gammaLinear_mixed u v)
  simpa only [pow_two] using h

#print axioms centeredProduct_gram
#print axioms sourceCenteredGammaPair_transpose
#print axioms sourceCenteredGammaPair_gram
#check @sourceCenteredGammaPair_gram

end
end FCP.BFSSSU2PhysicalDomainL6G5H
