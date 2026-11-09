import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5MSourceColorWedgeEnergyProbe

/-!
L6G5N — the actual finite real quartic contraction in the normalized
source Pauli SU(2) color basis. Combines accepted Clifford row Gram,
literal coefficient color regroup, and fixed-color Lagrange area.
No orbital/fermionic Gauss term, operator-domain extension, or spectrum.
-/
set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G5N
noncomputable section
open scoped Matrix BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G1
open FCP.BFSSSU2PhysicalDomainL6G2
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G5F
open FCP.BFSSSU2PhysicalDomainL6G5I
open FCP.BFSSSU2PhysicalDomainL6G5H
open FCP.BFSSSU2PhysicalDomainL6G5L
open FCP.BFSSSU2PhysicalDomainL6G5M

/-- Exact source coefficient-square energy at EACH actual color.
No unproved four-gamma cancellation: G/J/H/I/L/M supply the
source Pluecker/Jacobi, Clifford and normalization identities. -/
theorem sourceSU2FixedColorQuadraticEnergy
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (w : SpinIndex → ℝ) (x : Boson 2) (a : ColorIndex 2) :
    (1 / 2 : ℝ) * (∑ β : SpinIndex,
      (sourceQuadraticPointReal M w (β,a) x) ^ 2) =
      spinorSquareNorm w *
        ((1 / 4 : ℝ) * (∑ i : SpaceIndex, ∑ j : SpaceIndex,
          (M.coordinateBracketAll x i j a) ^ 2)) := by
  classical
  let u := sourceCyclicU x a
  let v := sourceCyclicV x a
  have hcoeff :
      (∑ β : SpinIndex,
        (sourceQuadraticPointReal M w (β,a) x) ^ 2) =
        (Real.sqrt 2) ^ 2 *
          (∑ β : SpinIndex,
            ((w ᵥ* sourceCenteredGammaPair M u v) β) ^ 2) := by
    calc
      _ = ∑ β : SpinIndex,
        (Real.sqrt 2 *
          ((w ᵥ* sourceCenteredGammaPair M u v) β)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro β _
            rw [sourceQuadraticReal_eq_cyclicCenteredRow M hcolor w x β a]
      _ = _ := by
            simp only [mul_pow]
            rw [Finset.mul_sum]
  calc
    (1 / 2 : ℝ) * (∑ β : SpinIndex,
        (sourceQuadraticPointReal M w (β,a) x) ^ 2) =
      (1 / 2 : ℝ) * ((Real.sqrt 2)^2 *
        ∑ β : SpinIndex,
          ((w ᵥ* sourceCenteredGammaPair M u v) β) ^ 2) := by rw [hcoeff]
    _ = ∑ β : SpinIndex,
          ((w ᵥ* sourceCenteredGammaPair M u v) β) ^ 2 := by
            rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
            ring
    _ = (((∑ i : SpaceIndex, u i ^ 2) *
          (∑ i : SpaceIndex, v i ^ 2)) -
          (∑ i : SpaceIndex, u i * v i) ^ 2) *
          spinorSquareNorm w := sourceCenteredGammaPair_rowGram M u v w
    _ = spinorSquareNorm w *
      ((1 / 4 : ℝ) * (∑ i : SpaceIndex, ∑ j : SpaceIndex,
        (M.coordinateBracketAll x i j a) ^ 2)) := by
          rw [sourceSU2ColorBracketEnergy_area M hcolor x a]
          ring

/-- FULL FINITE SOURCE QUARTIC IDENTITY: scalar source W coefficients
versus original nine-space bosonic commutator potential, with exact
factor 1/2 and ||w||², under explicit normalized-Pauli source color. -/
theorem sourceSU2FiniteQuarticReal
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (w : SpinIndex → ℝ) (x : Boson 2) :
    (1 / 2 : ℝ) * (∑ p : FermionLabel 2,
      (sourceQuadraticPointReal M w p x) ^ 2) =
        spinorSquareNorm w * sourceNineSpatialQuarticPotential M x := by
  classical
  have hpairs :
      (∑ p : FermionLabel 2,
        (sourceQuadraticPointReal M w p x) ^ 2) =
      (∑ a : ColorIndex 2, ∑ β : SpinIndex,
        (sourceQuadraticPointReal M w (β,a) x) ^ 2) := by
    simp only [Fintype.sum_prod_type]
    exact Finset.sum_comm
  have hcolors :
      (∑ i : SpaceIndex, ∑ j : SpaceIndex, ∑ a : ColorIndex 2,
        (M.coordinateBracketAll x i j a) ^ 2) =
      (∑ a : ColorIndex 2, ∑ i : SpaceIndex, ∑ j : SpaceIndex,
        (M.coordinateBracketAll x i j a) ^ 2) := by
    calc
      _ = ∑ i : SpaceIndex, ∑ a : ColorIndex 2, ∑ j : SpaceIndex,
        (M.coordinateBracketAll x i j a) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  calc
    (1 / 2 : ℝ) * (∑ p : FermionLabel 2,
        (sourceQuadraticPointReal M w p x) ^ 2) =
      ∑ a : ColorIndex 2, (1 / 2 : ℝ) *
        (∑ β : SpinIndex,
          (sourceQuadraticPointReal M w (β,a) x) ^ 2) := by
            rw [hpairs, Finset.mul_sum]
    _ = ∑ a : ColorIndex 2, spinorSquareNorm w *
      ((1 / 4 : ℝ) * (∑ i : SpaceIndex, ∑ j : SpaceIndex,
        (M.coordinateBracketAll x i j a) ^ 2)) := by
          apply Finset.sum_congr rfl
          intro a _
          exact sourceSU2FixedColorQuadraticEnergy M hcolor w x a
    _ = _ := by
      unfold sourceNineSpatialQuarticPotential
      rw [hcolors]
      simp only [Finset.mul_sum]

#print axioms sourceSU2FixedColorQuadraticEnergy
#print axioms sourceSU2FiniteQuarticReal
#check @sourceSU2FiniteQuarticReal
end
end FCP.BFSSSU2PhysicalDomainL6G5N
