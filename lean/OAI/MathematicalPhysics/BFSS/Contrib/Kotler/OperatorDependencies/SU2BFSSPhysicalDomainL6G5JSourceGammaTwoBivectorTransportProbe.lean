import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5IOriginalQuadraticRealAndGammaRowProbe
import Mathlib.Tactic.Module

/-!
L6G5J — source gammaTwo weighted tensor and decomposable wedge.
The same source gamma, ordered nine-space sum and original 1/2
are transported into the accepted centered Clifford matrix.
Color selection and quartic-potential assembly remain separate.
-/
set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G5J
noncomputable section
open scoped Matrix BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G5H

theorem sourceGammaTwo_alt {N : ℕ}
    (M : AlgebraData N) (i j : SpaceIndex) :
    M.gammaTwo i j =
      M.gamma i * M.gamma j -
        (if i = j then (1 : ℝ) else 0) • (1 : GammaMatrix) := by
  change OAI.BFSSGamma.gammaTwo M.gamma i j = _
  exact OAI.BFSSGamma.gammaTwo_alt M.gamma M.gamma_clifford i j

/-- Original gammaTwo, weighted across ALL nine ordered spatial pairs,
is the exact centered Clifford product, not a substitute matrix. -/
theorem sourceGammaTwo_weighted_centered {N : ℕ}
    (M : AlgebraData N) (u v : SpaceIndex → ℝ) :
    (∑ i : SpaceIndex, ∑ j : SpaceIndex,
      (u i * v j) • M.gammaTwo i j) =
        sourceCenteredGammaPair M u v := by
  classical
  have hprod (a b : SpaceIndex → ℝ) :
      (∑ i : SpaceIndex, a i • M.gamma i) *
        (∑ j : SpaceIndex, b j • M.gamma j) =
      ∑ i : SpaceIndex, ∑ j : SpaceIndex,
        (a i * b j) • (M.gamma i * M.gamma j) := by
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
      mul_smul_comm, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (b j) (a i)]
  have hdiag :
      (∑ i : SpaceIndex, ∑ j : SpaceIndex,
        (u i * v j) •
          ((if i = j then (1 : ℝ) else 0) • (1 : GammaMatrix))) =
      (∑ i : SpaceIndex, u i * v i) • (1 : GammaMatrix) := by
    calc
      _ = ∑ i : SpaceIndex, ∑ j : SpaceIndex,
        (if i = j then (u i * v i) • (1 : GammaMatrix) else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          by_cases hij : i = j
          · subst j
            simp
          · simp [hij]
      _ = ∑ i : SpaceIndex, (u i * v i) • (1 : GammaMatrix) := by
          simp
      _ = _ := by rw [Finset.sum_smul]
  calc
    (∑ i : SpaceIndex, ∑ j : SpaceIndex,
        (u i * v j) • M.gammaTwo i j) =
      (∑ i : SpaceIndex, ∑ j : SpaceIndex,
        (u i * v j) • (M.gamma i * M.gamma j)) -
      (∑ i : SpaceIndex, ∑ j : SpaceIndex,
        (u i * v j) •
          ((if i = j then (1 : ℝ) else 0) • (1 : GammaMatrix))) := by
            simp_rw [sourceGammaTwo_alt M, smul_sub,
              Finset.sum_sub_distrib]
    _ = M.gammaLinear u * M.gammaLinear v -
        (∑ i : SpaceIndex, u i * v i) • (1 : GammaMatrix) := by
          rw [← hprod u v, hdiag]
          rfl
    _ = sourceCenteredGammaPair M u v := rfl

/-- The antisymmetric color wedge with the original factor one-half
is the same centered matrix. Neither wedge orientation is discarded. -/
theorem sourceGammaTwo_wedge_centered {N : ℕ}
    (M : AlgebraData N) (u v : SpaceIndex → ℝ) :
    (1 / 2 : ℝ) •
      (∑ i : SpaceIndex, ∑ j : SpaceIndex,
        (u i * v j - u j * v i) • M.gammaTwo i j) =
          sourceCenteredGammaPair M u v := by
  classical
  have hrev :
      (∑ i : SpaceIndex, ∑ j : SpaceIndex,
        (u j * v i) • M.gammaTwo i j) =
      sourceCenteredGammaPair M v u := by
    calc
      _ = ∑ i : SpaceIndex, ∑ j : SpaceIndex,
        (v i * u j) • M.gammaTwo i j := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [mul_comm (u j) (v i)]
      _ = _ := sourceGammaTwo_weighted_centered M v u
  have hcenter :
      sourceCenteredGammaPair M u v +
        sourceCenteredGammaPair M v u = 0 := by
    have hd : (∑ i : SpaceIndex, v i * u i) =
        ∑ i : SpaceIndex, u i * v i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    unfold sourceCenteredGammaPair
    rw [hd]
    calc
      M.gammaLinear u * M.gammaLinear v -
        (∑ i : SpaceIndex, u i * v i) • (1 : GammaMatrix) +
        (M.gammaLinear v * M.gammaLinear u -
        (∑ i : SpaceIndex, u i * v i) • (1 : GammaMatrix)) =
      (M.gammaLinear u * M.gammaLinear v +
        M.gammaLinear v * M.gammaLinear u) -
        (2 * ∑ i : SpaceIndex, u i * v i) • (1 : GammaMatrix) := by
          module
      _ = 0 := by rw [M.gammaLinear_mixed u v]; module
  have hcv :
      sourceCenteredGammaPair M v u =
        -sourceCenteredGammaPair M u v := by
    calc
      _ = (sourceCenteredGammaPair M u v +
          sourceCenteredGammaPair M v u) -
            sourceCenteredGammaPair M u v := by abel
      _ = _ := by rw [hcenter]; abel
  calc
    (1 / 2 : ℝ) •
        (∑ i : SpaceIndex, ∑ j : SpaceIndex,
          (u i * v j - u j * v i) • M.gammaTwo i j) =
      (1 / 2 : ℝ) •
        (sourceCenteredGammaPair M u v -
          sourceCenteredGammaPair M v u) := by
            simp_rw [sub_smul, Finset.sum_sub_distrib]
            rw [sourceGammaTwo_weighted_centered M u v, hrev]
    _ = _ := by rw [hcv]; module

#print axioms sourceGammaTwo_alt
#print axioms sourceGammaTwo_weighted_centered
#print axioms sourceGammaTwo_wedge_centered
#check @sourceGammaTwo_wedge_centered
end
end FCP.BFSSSU2PhysicalDomainL6G5J
