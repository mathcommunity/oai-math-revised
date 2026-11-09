import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K9COrderedPairCoefficientProbe

/-!
# BFSS SU(2) G4-K9D — exact source potential multiplier equality

PROSPECTIVE / UNCOMPILED until a pinned GitHub Actions gate reports success.
The independent Grok derivation is a proof strategy, not compiler evidence.

Every BFSS quantity below is from openai/math at the frozen source pin.
The sole abstract result concerns a finite permutation of six summations.
Its hypotheses are fully visible; no gamma, theta, color or operator axiom
is introduced. Subsequent theorems compare the original source objects.
-/

namespace FCP.BFSSSU2GaugeG4K9D
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open Finset
open FCP.BFSSSU2GaugeG4K9C

/-- A finite six-index sum can be regrouped around the spin/color
operator indices without changing any coefficients. -/
private theorem reorderSixFiniteSums
    {N : ℕ} {E : Type*} [AddCommMonoid E]
    (u : SpaceIndex → SpaceIndex → ColorIndex N → ColorIndex N →
      ColorIndex N → SpinIndex → E) :
    (∑ i : SpaceIndex, ∑ j : SpaceIndex, ∑ A : ColorIndex N,
      ∑ B : ColorIndex N, ∑ C : ColorIndex N, ∑ β : SpinIndex,
        u i j A B C β) =
      ∑ β : SpinIndex, ∑ A : ColorIndex N, ∑ i : SpaceIndex,
        ∑ j : SpaceIndex, ∑ B : ColorIndex N, ∑ C : ColorIndex N,
          u i j A B C β := by
  calc
    (∑ i : SpaceIndex, ∑ j : SpaceIndex, ∑ A : ColorIndex N,
      ∑ B : ColorIndex N, ∑ C : ColorIndex N, ∑ β : SpinIndex,
        u i j A B C β) =
      ∑ i : SpaceIndex, ∑ j : SpaceIndex, ∑ A : ColorIndex N,
        ∑ β : SpinIndex, ∑ B : ColorIndex N, ∑ C : ColorIndex N,
          u i j A B C β := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro A _
            calc
              (∑ B : ColorIndex N, ∑ C : ColorIndex N,
                ∑ β : SpinIndex, u i j A B C β) =
                  ∑ B : ColorIndex N, ∑ β : SpinIndex,
                    ∑ C : ColorIndex N, u i j A B C β := by
                      apply Finset.sum_congr rfl
                      intro B _
                      exact Finset.sum_comm
              _ = ∑ β : SpinIndex, ∑ B : ColorIndex N,
                    ∑ C : ColorIndex N, u i j A B C β := Finset.sum_comm
    _ = (∑ i : SpaceIndex, ∑ j : SpaceIndex, ∑ β : SpinIndex,
          ∑ A : ColorIndex N, ∑ B : ColorIndex N, ∑ C : ColorIndex N,
            u i j A B C β) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact Finset.sum_comm
    _ = (∑ i : SpaceIndex, ∑ β : SpinIndex, ∑ j : SpaceIndex,
          ∑ A : ColorIndex N, ∑ B : ColorIndex N, ∑ C : ColorIndex N,
            u i j A B C β) := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
    _ = (∑ β : SpinIndex, ∑ i : SpaceIndex, ∑ j : SpaceIndex,
          ∑ A : ColorIndex N, ∑ B : ColorIndex N, ∑ C : ColorIndex N,
            u i j A B C β) := Finset.sum_comm
    _ = (∑ β : SpinIndex, ∑ i : SpaceIndex, ∑ A : ColorIndex N,
          ∑ j : SpaceIndex, ∑ B : ColorIndex N, ∑ C : ColorIndex N,
            u i j A B C β) := by
          apply Finset.sum_congr rfl
          intro β _
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
    _ = ∑ β : SpinIndex, ∑ A : ColorIndex N, ∑ i : SpaceIndex,
          ∑ j : SpaceIndex, ∑ B : ColorIndex N, ∑ C : ColorIndex N,
            u i j A B C β := by
          apply Finset.sum_congr rfl
          intro β _
          exact Finset.sum_comm

/-- The qualified original six-index coefficient, expressed through
the genuine original source structure constants and gammaTwo, expands
to the same scalar used by the original bracketMultiplier definition. -/
private theorem sourcePotentialCoefficientExpanded
    {N : ℕ} (M : AlgebraData N) (x : Boson N)
    (α β : SpinIndex) (A : ColorIndex N) :
    (M.deformedPotentialCoefficients 1 0 x α (β, A) : ℂ) =
      ∑ i : SpaceIndex, ∑ j : SpaceIndex,
      ∑ B : ColorIndex N, ∑ C : ColorIndex N,
        ((((1 / 2 : ℝ) * M.structureConstant A B C *
          M.gammaTwo i j α β : ℝ) : ℂ) *
          (x (i, B) : ℂ) * (x (j, C) : ℂ)) := by
  have hreal :
      (1 / 2 : ℝ) * (∑ i : SpaceIndex, ∑ j : SpaceIndex,
        M.coordinateBracketAll x i j A * M.gammaTwo i j α β) =
        ∑ i : SpaceIndex, ∑ j : SpaceIndex,
        ∑ B : ColorIndex N, ∑ C : ColorIndex N,
          (1 / 2 : ℝ) * M.structureConstant A B C *
            M.gammaTwo i j α β * x (i, B) * x (j, C) := by
    simp only [AlgebraData.coordinateBracketAll,
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro B _
    apply Finset.sum_congr rfl
    intro C _
    ring
  rw [sourceMasslessCoefficient_eq_halfOriginalOrdered M x α β A]
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul] using
    congrArg (fun z : ℝ => (z : ℂ)) hreal

/-- Unconditional equality of the two ORIGINAL source potential
multipliers at the undeformed massless parameters h=1,m=0. -/
theorem sourcePotentialMultipliers_equal
    {N : ℕ} (M : AlgebraData N) (α : SpinIndex) (x : Boson N) :
    M.deformedPotentialMultiplier 1 0 x α = M.bracketMultiplier α x := by
  have hrev :
      M.bracketMultiplier α x =
        ∑ β : SpinIndex, ∑ A : ColorIndex N, ∑ i : SpaceIndex,
        ∑ j : SpaceIndex, ∑ B : ColorIndex N, ∑ C : ColorIndex N,
          ((((1 / 2 : ℝ) * M.structureConstant A B C *
            M.gammaTwo i j α β : ℝ) : ℂ) *
            (x (i, B) : ℂ) * (x (j, C) : ℂ)) • M.theta β A := by
    unfold AlgebraData.bracketMultiplier
    exact reorderSixFiniteSums (fun i j A B C β =>
      ((((1 / 2 : ℝ) * M.structureConstant A B C *
        M.gammaTwo i j α β : ℝ) : ℂ) *
        (x (i, B) : ℂ) * (x (j, C) : ℂ)) • M.theta β A)
  calc
    M.deformedPotentialMultiplier 1 0 x α =
        ∑ β : SpinIndex, ∑ A : ColorIndex N,
          (M.deformedPotentialCoefficients 1 0 x α (β, A) : ℂ) •
            M.theta β A := by
              simp only [deformedPotentialMultiplier, cliffordLinear,
                Fintype.sum_prod_type]
    _ = ∑ β : SpinIndex, ∑ A : ColorIndex N,
          (∑ i : SpaceIndex, ∑ j : SpaceIndex,
            ∑ B : ColorIndex N, ∑ C : ColorIndex N,
              ((((1 / 2 : ℝ) * M.structureConstant A B C *
                M.gammaTwo i j α β : ℝ) : ℂ) *
                (x (i, B) : ℂ) * (x (j, C) : ℂ))) •
            M.theta β A := by
              apply Finset.sum_congr rfl
              intro β _
              apply Finset.sum_congr rfl
              intro A _
              rw [sourcePotentialCoefficientExpanded M x α β A]
    _ = ∑ β : SpinIndex, ∑ A : ColorIndex N, ∑ i : SpaceIndex,
          ∑ j : SpaceIndex, ∑ B : ColorIndex N, ∑ C : ColorIndex N,
            ((((1 / 2 : ℝ) * M.structureConstant A B C *
              M.gammaTwo i j α β : ℝ) : ℂ) *
              (x (i, B) : ℂ) * (x (j, C) : ℂ)) • M.theta β A := by
              -- Fold the RHS finite sums of scalar multiples through
              -- the fixed, original theta operator at each spin/color index.
              apply Finset.sum_congr rfl
              intro β _
              apply Finset.sum_congr rfl
              intro A _
              simp only [← Finset.sum_smul]
    _ = M.bracketMultiplier α x := hrev.symm

/-- The pinned G4-K9B conditional all-core result can now be specialized
without any additional assumption, once the multiplier equality is checked. -/
theorem sourceUnconditionalCoreCharge_equal
    {N : ℕ} (M : AlgebraData N) (α : SpinIndex) (f : SmoothCore N) :
    M.deformedCoreCharge 1 0 α f = M.charge α f := by
  exact FCP.BFSSSU2GaugeG4K9B.sourceCharge_eq_of_potentialAgreement
    M α (fun x => sourcePotentialMultipliers_equal M α x) f

/-- Exact original source core quadratic-form identity on SmoothCore N. -/
theorem sourceUnconditionalCoreForm_equal
    {N : ℕ} (M : AlgebraData N) (f : SmoothCore N) :
    M.deformedCoreEnergy 1 0 f = M.coreForm f := by
  exact FCP.BFSSSU2GaugeG4K9B.sourceCoreForm_eq_of_potentialAgreement
    M (fun α x => sourcePotentialMultipliers_equal M α x) f

#print axioms sourcePotentialCoefficientExpanded
#print axioms sourcePotentialMultipliers_equal
#print axioms sourceUnconditionalCoreCharge_equal
#print axioms sourceUnconditionalCoreForm_equal

end
end FCP.BFSSSU2GaugeG4K9D
