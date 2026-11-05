import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5SOriginalSignedRowGammaContractionProbe

/-!
L6G5T — original signed gamma/color bracket collapse.

L6G5S has proved the actual original real spinor-row gamma contraction.
The pinned mathematical source already proves coordinateBracketAll_skew
for its genuine structure constants. Their composition below cancels
the two ordered spatial Kronecker contributions by a finite reindex,
with the exact minus-two coefficient. No replacement SU(2) tensor,
full differential operator, Gauss, or spectrum is assumed.
-/

set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G5T
noncomputable section
open scoped Matrix BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G1
open FCP.BFSSSU2PhysicalDomainL6G5S

/-- Universal finite-index identity: contracting both Kronecker legs
against a skew spatial bracket produces MINUS TWO times its ordered
right-hand leg. The sign comes from swapping the bracket indices,
not an assumption about the zero of either individual summand. -/
private theorem skewKronecker_contraction
    {I : Type*} [Fintype I] [DecidableEq I]
    (B : I → I → ℝ)
    (hskew : ∀ j k : I, B j k = -B k j)
    (v : I → ℝ) (i : I) :
    (∑ j : I, ∑ k : I,
      B j k *
        ((if i = k then v j else 0) -
         (if i = j then v k else 0))) =
      (-2 : ℝ) * ∑ k : I, B i k * v k := by
  classical
  have hfirst (j : I) :
      (∑ k : I, B j k * (if i = k then v j else 0)) =
        B j i * v j := by
    simp [mul_ite]
  have hsecond (k : I) :
      (∑ j : I, B j k * (if i = j then v k else 0)) =
        B i k * v k := by
    simp [mul_ite]
  have hsumfirst :
      (∑ j : I, ∑ k : I, B j k *
        (if i = k then v j else 0)) =
        ∑ j : I, B j i * v j := by
    apply Finset.sum_congr rfl
    intro j _
    exact hfirst j
  have hsumsecond :
      (∑ j : I, ∑ k : I, B j k *
        (if i = j then v k else 0)) =
        ∑ k : I, B i k * v k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    exact hsecond k
  have hswap :
      (∑ j : I, B j i * v j) =
        -(∑ j : I, B i j * v j) := by
    calc
      _ = ∑ j : I, (-B i j) * v j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hskew j i]
      _ = _ := by
        simp only [neg_mul, Finset.sum_neg_distrib]
  calc
    (∑ j : I, ∑ k : I,
        B j k *
          ((if i = k then v j else 0) -
           (if i = j then v k else 0))) =
      (∑ j : I, ∑ k : I,
        B j k * (if i = k then v j else 0)) -
      (∑ j : I, ∑ k : I,
        B j k * (if i = j then v k else 0)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ = (∑ j : I, B j i * v j) -
        (∑ k : I, B i k * v k) := by
      rw [hsumfirst, hsumsecond]
    _ = (-2 : ℝ) * ∑ k : I, B i k * v k := by
      rw [hswap]
      ring

/-- Signed original spinor contraction summed against the exact
source bosonic coordinate bracket, at every individual source color
and every spatial derivative label. No normalized-Pauli color
assumption is needed because source bracket skew is already proven
for each AlgebraData. -/
theorem sourceOriginalGammaColorBracket_mixedContraction
    {N : ℕ} (M : AlgebraData N)
    (hgamma : M.gamma = originalGamma)
    (w : SpinIndex → ℝ) (x : Boson N)
    (i : SpaceIndex) (a : ColorIndex N) :
    (∑ j : SpaceIndex, ∑ k : SpaceIndex,
      M.coordinateBracketAll x j k a *
        (∑ β : SpinIndex,
          (w ᵥ* M.gamma i) β *
          (w ᵥ* M.gammaTwo j k) β)) =
      (-2 : ℝ) * (∑ k : SpaceIndex,
        M.coordinateBracketAll x i k a *
          dotProduct w (M.gamma k *ᵥ w)) := by
  simp_rw [sourceOriginalGamma_row_bivector_contraction M hgamma w i]
  exact skewKronecker_contraction
    (fun j k : SpaceIndex => M.coordinateBracketAll x j k a)
    (fun j k => M.coordinateBracketAll_skew x k j a)
    (fun k : SpaceIndex => dotProduct w (M.gamma k *ᵥ w)) i

#print axioms skewKronecker_contraction
#print axioms sourceOriginalGammaColorBracket_mixedContraction
#check @sourceOriginalGammaColorBracket_mixedContraction
end
end FCP.BFSSSU2PhysicalDomainL6G5T
