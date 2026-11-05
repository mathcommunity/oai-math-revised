import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5JSourceGammaTwoBivectorTransportProbe

/-!
L6G5K: exact original source real quadratic coefficient, reindexed into
its pinned coordinateBracketAll (same structure constants, gammaTwo,
ordered spatial positions and factor 1/2). This is a finite Fubini
reindexing, NOT a new color/gamma or potential identity.
-/
set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G5K
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G4A
open FCP.BFSSSU2PhysicalDomainL6G5I

private theorem finitePairSum_fourfold
    {I A : Type*} [Fintype I] [Fintype A] (g : I → I → A → A → ℝ) :
    (∑ v : I × A, ∑ t : I × A, g v.1 t.1 v.2 t.2) =
      ∑ i : I, ∑ j : I, ∑ b : A, ∑ c : A, g i j b c := by
  classical
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

/-- No Pauli premise: only the original color bracket definition and
a legally reordered finite sum of unchanged source coefficients. -/
theorem sourceQuadraticReal_eq_bracket_sum {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ)
    (β : SpinIndex) (a : ColorIndex N) (x : Boson N) :
    sourceQuadraticPointReal M w (β,a) x =
      ∑ α : SpinIndex, w α *
        (∑ i : SpaceIndex, ∑ j : SpaceIndex,
          ((1 / 2 : ℝ) * M.coordinateBracketAll x i j a) *
            M.gammaTwo i j α β) := by
  classical
  unfold sourceQuadraticPointReal
  apply Finset.sum_congr rfl
  intro α _
  congr 1
  calc
    (∑ v : BosonLabel N, ∑ t : BosonLabel N,
        ((1 / 2 : ℝ) * M.structureConstant a v.2 t.2 *
          M.gammaTwo v.1 t.1 α β) * x v * x t) =
      ∑ i : SpaceIndex, ∑ j : SpaceIndex,
        ∑ b : ColorIndex N, ∑ c : ColorIndex N,
          ((1 / 2 : ℝ) * M.structureConstant a b c *
            M.gammaTwo i j α β) * x (i,b) * x (j,c) := by
              exact finitePairSum_fourfold (fun i j b c =>
                ((1 / 2 : ℝ) * M.structureConstant a b c *
                  M.gammaTwo i j α β) * x (i,b) * x (j,c))
    _ = ∑ i : SpaceIndex, ∑ j : SpaceIndex,
          ((1 / 2 : ℝ) * M.coordinateBracketAll x i j a) *
            M.gammaTwo i j α β := by
          unfold coordinateBracketAll
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro c _
          ring

#print axioms finitePairSum_fourfold
#print axioms sourceQuadraticReal_eq_bracket_sum
#check @sourceQuadraticReal_eq_bracket_sum
end
end FCP.BFSSSU2PhysicalDomainL6G5K
