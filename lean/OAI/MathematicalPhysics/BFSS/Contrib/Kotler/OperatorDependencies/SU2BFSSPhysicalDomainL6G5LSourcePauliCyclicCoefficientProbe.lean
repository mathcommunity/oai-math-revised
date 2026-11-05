import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5KSourceQuadraticBracketRegroupProbe

/-!
L6G5L: original source real quadratic coefficient at every actual
SU(2) color label equals sqrt(2) times the cyclic centered gamma row.
The source normalized-Pauli premise is EXPLICIT and supplies the
unchanged structure constants f_abc=sqrt(2) epsilon_abc.
The final squared-color sum to the potential remains a separate gate.
-/
set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G5L
noncomputable section
open scoped Matrix BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G5G
open FCP.BFSSSU2PhysicalDomainL6G5H
open FCP.BFSSSU2PhysicalDomainL6G5I
open FCP.BFSSSU2PhysicalDomainL6G5J
open FCP.BFSSSU2PhysicalDomainL6G5K

/-- Positively oriented first complementary color coordinate vector. -/
def sourceCyclicU (x : Boson 2) (a : Fin 3) : SpaceIndex → ℝ :=
  fun i => if a = 0 then x (i,(1 : Fin 3))
    else if a = 1 then x (i,(2 : Fin 3)) else x (i,(0 : Fin 3))

/-- Positively oriented second complementary color coordinate vector. -/
def sourceCyclicV (x : Boson 2) (a : Fin 3) : SpaceIndex → ℝ :=
  fun i => if a = 0 then x (i,(2 : Fin 3))
    else if a = 1 then x (i,(0 : Fin 3)) else x (i,(1 : Fin 3))

/-- Actual source bracket at fixed color is a simple oriented
bivector, derived from the accepted Pauli color structure constants. -/
theorem sourceSU2Bracket_eq_cyclicWedge
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (x : Boson 2) (a : ColorIndex 2) (i j : SpaceIndex) :
    M.coordinateBracketAll x i j a =
      Real.sqrt 2 * (sourceCyclicU x a i * sourceCyclicV x a j -
        sourceCyclicU x a j * sourceCyclicV x a i) := by
  rw [sourceSU2Bracket_eq_cross M hcolor x i j a]
  fin_cases a <;>
    simp [sourceCyclicU, sourceCyclicV, FCP.BFSSSU2.colorCross] <;>
    ring

/-- The literal original color coefficient is the corresponding
source-defined centered Clifford row, including the correct sqrt(2). -/
theorem sourceQuadraticReal_eq_cyclicCenteredRow
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (w : SpinIndex → ℝ) (x : Boson 2)
    (β : SpinIndex) (a : ColorIndex 2) :
    sourceQuadraticPointReal M w (β,a) x =
      Real.sqrt 2 *
        (w ᵥ* sourceCenteredGammaPair M
          (sourceCyclicU x a) (sourceCyclicV x a)) β := by
  classical
  let u := sourceCyclicU x a
  let v := sourceCyclicV x a
  have hmat :
      (∑ i : SpaceIndex, ∑ j : SpaceIndex,
        ((1 / 2 : ℝ) * M.coordinateBracketAll x i j a) •
          M.gammaTwo i j) =
        Real.sqrt 2 • sourceCenteredGammaPair M u v := by
    calc
      _ = Real.sqrt 2 • ((1 / 2 : ℝ) •
        (∑ i : SpaceIndex, ∑ j : SpaceIndex,
          (u i * v j - u j * v i) • M.gammaTwo i j)) := by
            simp_rw [sourceSU2Bracket_eq_cyclicWedge M hcolor x a]
            simp only [Finset.smul_sum, smul_smul]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            congr 1
            ring
      _ = _ := by rw [sourceGammaTwo_wedge_centered M u v]
  have hentry (α β : SpinIndex) :
      (∑ i : SpaceIndex, ∑ j : SpaceIndex,
        ((1 / 2 : ℝ) * M.coordinateBracketAll x i j a) *
          M.gammaTwo i j α β) =
        Real.sqrt 2 * (sourceCenteredGammaPair M u v) α β := by
    have h := congrArg (fun T : GammaMatrix => T α β) hmat
    change (∑ i : SpaceIndex, ∑ j : SpaceIndex,
      ((1 / 2 : ℝ) * M.coordinateBracketAll x i j a) *
        M.gammaTwo i j α β) =
          Real.sqrt 2 * (sourceCenteredGammaPair M u v) α β at h
    exact h
  rw [sourceQuadraticReal_eq_bracket_sum M w β a x]
  simp_rw [hentry]
  change (∑ α : SpinIndex,
      w α * (Real.sqrt 2 * (sourceCenteredGammaPair M u v) α β)) =
    Real.sqrt 2 *
      (∑ α : SpinIndex, w α * (sourceCenteredGammaPair M u v) α β)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  ring

#print axioms sourceSU2Bracket_eq_cyclicWedge
#print axioms sourceQuadraticReal_eq_cyclicCenteredRow
#check @sourceQuadraticReal_eq_cyclicCenteredRow
end
end FCP.BFSSSU2PhysicalDomainL6G5L
