import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5TOriginalMixedBracketReindexProbe

/-!
L6G5U: identify the original real quadratic point coefficient with
a source gammaTwo row and collapse its exact mixed coefficient against
the original -i kinetic gamma row. This is finite, pointwise, and
unconditional beyond the explicit source gamma matching premise.

The result is the immediate scalar input for the genuinely RIGHT-ordered
SmoothCore first-order mixed operator. No operator-order swapping, Gauss
identification, restriction to physical vectors, or spectral assertion.
-/

set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G5U
noncomputable section
open scoped Matrix BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G1
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G5I
open FCP.BFSSSU2PhysicalDomainL6G5K
open FCP.BFSSSU2PhysicalDomainL6G5T

/-- The pinned quadratic source W_{βa}(x) is a half-weighted
source bracket times the literal gammaTwo spinor ROW. Nothing about
Pauli color, spinor norm, or gamma representation is assumed. -/
theorem sourceQuadraticPointReal_eq_bracketRow
    {N : ℕ} (M : AlgebraData N)
    (w : SpinIndex → ℝ) (β : SpinIndex)
    (a : ColorIndex N) (x : Boson N) :
    sourceQuadraticPointReal M w (β,a) x =
      ∑ j : SpaceIndex, ∑ k : SpaceIndex,
        ((1 / 2 : ℝ) * M.coordinateBracketAll x j k a) *
          ((w ᵥ* M.gammaTwo j k) β) := by
  rw [sourceQuadraticReal_eq_bracket_sum]
  calc
    (∑ α : SpinIndex, w α *
      (∑ j : SpaceIndex, ∑ k : SpaceIndex,
        ((1 / 2 : ℝ) * M.coordinateBracketAll x j k a) *
          M.gammaTwo j k α β)) =
      ∑ α : SpinIndex, ∑ j : SpaceIndex, ∑ k : SpaceIndex,
        w α * (((1 / 2 : ℝ) *
          M.coordinateBracketAll x j k a) *
          M.gammaTwo j k α β) := by
            simp only [Finset.mul_sum]
    _ = ∑ j : SpaceIndex, ∑ k : SpaceIndex, ∑ α : SpinIndex,
        w α * (((1 / 2 : ℝ) *
          M.coordinateBracketAll x j k a) *
          M.gammaTwo j k α β) := by
            calc
              _ = ∑ j : SpaceIndex, ∑ α : SpinIndex,
                    ∑ k : SpaceIndex,
                      w α * (((1 / 2 : ℝ) *
                        M.coordinateBracketAll x j k a) *
                        M.gammaTwo j k α β) := Finset.sum_comm
              _ = _ := by
                apply Finset.sum_congr rfl
                intro j _
                exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      change (∑ α : SpinIndex,
          w α * (((1 / 2 : ℝ) * M.coordinateBracketAll x j k a) *
            M.gammaTwo j k α β)) =
        ((1 / 2 : ℝ) * M.coordinateBracketAll x j k a) *
          (∑ α : SpinIndex, w α * M.gammaTwo j k α β)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro α _
      ring

/-- Universal finite Fubini and scalar-half transport. The proof
does not change order of endomorphism products, since the theorem
is strictly about real scalar coefficients. -/
private theorem finiteMixedRow_halfFubini
    {A I : Type*} [Fintype A] [Fintype I]
    (r : A → ℝ) (B : I → I → ℝ) (q : I → I → A → ℝ) :
    (∑ β : A, r β * (∑ j : I, ∑ k : I,
        ((1 / 2 : ℝ) * B j k) * q j k β)) =
      (1 / 2 : ℝ) *
        (∑ j : I, ∑ k : I,
          B j k * (∑ β : A, r β * q j k β)) := by
  calc
    _ = ∑ β : A, ∑ j : I, ∑ k : I,
      (1 / 2 : ℝ) * (B j k * (r β * q j k β)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro β _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ = ∑ j : I, ∑ k : I, ∑ β : A,
      (1 / 2 : ℝ) * (B j k * (r β * q j k β)) := by
        calc
          _ = ∑ j : I, ∑ β : A, ∑ k : I,
            (1 / 2 : ℝ) * (B j k * (r β * q j k β)) :=
              Finset.sum_comm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro j _
            exact Finset.sum_comm
    _ = _ := by
      simp only [← Finset.mul_sum]

/-- The actual source W(x) coefficient against the unmodified real
kinetic gamma row is precisely minus the source color bracket
contracted with w^T gamma w. The -i kinetic factor is NOT included
yet: multiplying this identity by -i produces +i in the next gate. -/
theorem sourceOriginalMixedPointCoefficient_contract
    {N : ℕ} (M : AlgebraData N)
    (hgamma : M.gamma = originalGamma)
    (w : SpinIndex → ℝ) (x : Boson N)
    (i : SpaceIndex) (a : ColorIndex N) :
    (∑ β : SpinIndex,
      ((w ᵥ* M.gamma i) β) *
        sourceQuadraticPointReal M w (β,a) x) =
      -(∑ k : SpaceIndex,
        M.coordinateBracketAll x i k a *
          dotProduct w (M.gamma k *ᵥ w)) := by
  simp_rw [sourceQuadraticPointReal_eq_bracketRow]
  rw [finiteMixedRow_halfFubini
    (fun β : SpinIndex => (w ᵥ* M.gamma i) β)
    (fun j k : SpaceIndex => M.coordinateBracketAll x j k a)
    (fun j k β => (w ᵥ* M.gammaTwo j k) β)]
  rw [sourceOriginalGammaColorBracket_mixedContraction M hgamma w x i a]
  ring

#print axioms sourceQuadraticPointReal_eq_bracketRow
#print axioms finiteMixedRow_halfFubini
#print axioms sourceOriginalMixedPointCoefficient_contract
#check @sourceOriginalMixedPointCoefficient_contract
end
end FCP.BFSSSU2PhysicalDomainL6G5U
