import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5ROriginalGammaBivectorCommutatorProbe

/-!
L6G5S: the signed ORIGINAL row-spinor contraction. Reuses L6G2's
accepted originalGamma row/column sign and L6G5R's original-source
Clifford bivector commutator. No enumeration of 9^3 cases and no
assumed cancellation of symmetric/skew products.

This is a finite matrix theorem for arbitrary real spinors, including
zero. Its use in the original source first-order mixed operator and
orbital Gauss remains a later, separately qualified step.
-/

set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G5S
noncomputable section
open scoped Matrix BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G1
open FCP.BFSSSU2PhysicalDomainL6G2
open FCP.BFSSSU2PhysicalDomainL6G5R

/-- The original row contraction contains the crucial NEGATIVE
gammaTwo-transpose sign. The identity is valid without unit-norm
assumptions and keeps source-defined gamma labels. -/
theorem sourceOriginalGamma_row_bivector_contraction
    {N : ℕ} (M : AlgebraData N)
    (hgamma : M.gamma = originalGamma)
    (w : SpinIndex → ℝ) (i j k : SpaceIndex) :
    (∑ β : SpinIndex,
      (w ᵥ* M.gamma i) β * (w ᵥ* M.gammaTwo j k) β) =
        (if i = k then dotProduct w (M.gamma j *ᵥ w) else 0) -
        (if i = j then dotProduct w (M.gamma k *ᵥ w) else 0) := by
  have hrowG : w ᵥ* M.gamma i = M.gamma i *ᵥ w := by
    rw [hgamma]
    exact originalGamma_row_eq_column w i
  have hrowTwo :
      w ᵥ* M.gammaTwo j k = -(M.gammaTwo j k *ᵥ w) := by
    change w ᵥ* OAI.BFSSGamma.gammaTwo M.gamma j k =
      -(OAI.BFSSGamma.gammaTwo M.gamma j k *ᵥ w)
    rw [hgamma]
    exact originalGammaTwo_row_eq_neg_column w j k
  have hdot :
      dotProduct (M.gamma i *ᵥ w) (M.gammaTwo j k *ᵥ w) =
      dotProduct w ((M.gamma i * M.gammaTwo j k) *ᵥ w) := by
    rw [OAI.BFSSGamma.dot_mulVec_left,
      (M.gamma_symmetric i).eq, Matrix.mulVec_mulVec]
  have htranspose :
      (M.gamma i * M.gammaTwo j k).transpose =
        -(M.gammaTwo j k * M.gamma i) := by
    rw [Matrix.transpose_mul, sourceGammaTwo_skew_transpose,
      (M.gamma_symmetric i).eq, neg_mul]
  have hswap :
      dotProduct w ((M.gammaTwo j k * M.gamma i) *ᵥ w) =
        -dotProduct w ((M.gamma i * M.gammaTwo j k) *ᵥ w) := by
    have ht := OAI.BFSSGamma.dot_transpose
      (M.gamma i * M.gammaTwo j k) w
    rw [htranspose, Matrix.neg_mulVec, dotProduct_neg] at ht
    linarith
  have hcomm := congrArg
      (fun A : GammaMatrix => dotProduct w (A *ᵥ w))
      (sourceGamma_bivector_commutator M i j k)
  simp only [Matrix.sub_mulVec, dotProduct_sub,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hcomm
  have hscalar :
      dotProduct w ((M.gamma i * M.gammaTwo j k) *ᵥ w) =
        (if i = j then dotProduct w (M.gamma k *ᵥ w) else 0) -
        (if i = k then dotProduct w (M.gamma j *ᵥ w) else 0) := by
    rw [hswap] at hcomm
    have hfactor (P : Prop) [Decidable P] (a : ℝ) :
        (if P then (2 : ℝ) else 0) * a =
          2 * (if P then a else 0) := by
      by_cases hP : P <;> simp [hP]
    simp only [hfactor] at hcomm
    linarith
  calc
    (∑ β : SpinIndex,
      (w ᵥ* M.gamma i) β * (w ᵥ* M.gammaTwo j k) β) =
      -(dotProduct (M.gamma i *ᵥ w) (M.gammaTwo j k *ᵥ w)) := by
        change dotProduct (w ᵥ* M.gamma i)
          (w ᵥ* M.gammaTwo j k) = _
        rw [hrowG, hrowTwo, dotProduct_neg]
    _ = -(dotProduct w ((M.gamma i * M.gammaTwo j k) *ᵥ w)) := by
      rw [hdot]
    _ = _ := by rw [hscalar]; ring

#print axioms sourceOriginalGamma_row_bivector_contraction
#check @sourceOriginalGamma_row_bivector_contraction
end
end FCP.BFSSSU2PhysicalDomainL6G5S
