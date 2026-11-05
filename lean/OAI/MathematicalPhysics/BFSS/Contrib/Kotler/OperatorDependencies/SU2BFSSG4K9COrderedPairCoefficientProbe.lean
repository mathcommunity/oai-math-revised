import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K9BSourcePairAndChargeReductionProbe

/-!
# BFSS SU(2) G4-K9C — original ordered-pair to upper-triangle coefficient

UNCOMPILED CANDIDATE, not an accepted theorem until independently verified
at the exact Lean/Mathlib/OpenAI pins. The scientific goal is to discharge
the *actual* source finite-sum parity/reindexing step. Nothing here assumes
or yet proves the all-Fermion multiplier or closed-Hamiltonian equality.
-/

namespace FCP.BFSSSU2GaugeG4K9C
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open Finset
open FCP.BFSSSU2GaugeG4K9A
open FCP.BFSSSU2GaugeG4K9B

/-- Any symmetric real finite-pair summand vanishing on the diagonal:
the half-weighted full ordered sum equals its strict upper-triangle sum.
This is abstract combinatorics with ALL assumptions displayed. -/
theorem symmetricZeroDiagonal_halfDoubleSum_eq_upper
    (F : SpaceIndex → SpaceIndex → ℝ)
    (hsym : ∀ i j, F i j = F j i)
    (hdiag : ∀ i, F i i = 0) :
    (1 / 2 : ℝ) * (∑ i : SpaceIndex, ∑ j : SpaceIndex, F i j) =
      ∑ p : BFSSGamma.SpatialPair, F p.1.1 p.1.2 := by
  classical
  let upper : ℝ := ∑ i : SpaceIndex, ∑ j : SpaceIndex,
    if i < j then F i j else 0
  have hsplit (i j : SpaceIndex) :
      F i j =
        (if i < j then F i j else 0) +
          (if j < i then F i j else 0) := by
    rcases lt_trichotomy i j with hij | hij | hji
    · have hji : ¬ j < i := not_lt.mpr (le_of_lt hij)
      simp [hij, hji]
    · subst j
      simp [hdiag i]
    · have hij : ¬ i < j := not_lt.mpr (le_of_lt hji)
      simp [hij, hji]
  have hlow :
      (∑ i : SpaceIndex, ∑ j : SpaceIndex,
        if j < i then F i j else 0) = upper := by
    calc
      (∑ i : SpaceIndex, ∑ j : SpaceIndex,
        if j < i then F i j else 0) =
          ∑ i : SpaceIndex, ∑ j : SpaceIndex,
            if i < j then F j i else 0 := by
              rw [Finset.sum_comm]
      _ = upper := by
        dsimp [upper]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i < j
        · simp [hij, hsym]
        · simp [hij]
  have htwo :
      (∑ i : SpaceIndex, ∑ j : SpaceIndex, F i j) = upper + upper := by
    calc
      (∑ i : SpaceIndex, ∑ j : SpaceIndex, F i j) =
        ∑ i : SpaceIndex, ∑ j : SpaceIndex,
          ((if i < j then F i j else 0) +
            (if j < i then F i j else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact hsplit i j
      _ = upper + (∑ i : SpaceIndex, ∑ j : SpaceIndex,
        if j < i then F i j else 0) := by
          simp only [Finset.sum_add_distrib, upper]
      _ = upper + upper := by rw [hlow]
  have hupper :
      (∑ p : BFSSGamma.SpatialPair, F p.1.1 p.1.2) = upper := by
    dsimp [upper]
    -- The generic rewrite cannot synthesize the pair-function from
    -- `F p.1 p.2` under a dependent subtype binder. Give the exact
    -- original pair-indexed function to the mathlib theorem explicitly.
    -- The subtype's universe, filter sum, and product sum are converted
    -- only AFTER this source-independent typed equality has been formed.
    simpa only [Finset.subtype_univ, Finset.sum_filter,
      Fintype.sum_prod_type] using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset (SpaceIndex × SpaceIndex)))
        (p := fun ij : SpaceIndex × SpaceIndex => ij.1 < ij.2)
        (fun ij : SpaceIndex × SpaceIndex => F ij.1 ij.2))
  calc
    (1 / 2 : ℝ) * (∑ i : SpaceIndex, ∑ j : SpaceIndex, F i j) =
        upper := by rw [htwo]; ring
    _ = ∑ p : BFSSGamma.SpatialPair, F p.1.1 p.1.2 := hupper.symm

/-- The original color-bracket times gammaTwo coefficient is symmetric
in the two spatial coordinates: *both* source factors are antisymmetric. -/
theorem sourceOrderedCoefficient_symmetric
    {N : ℕ} (M : AlgebraData N) (x : Boson N)
    (α β : SpinIndex) (A : ColorIndex N)
    (i j : SpaceIndex) :
    M.coordinateBracketAll x i j A * M.gammaTwo i j α β =
      M.coordinateBracketAll x j i A * M.gammaTwo j i α β := by
  have hb := M.coordinateBracketAll_skew x i j A
  have hg : M.gammaTwo j i = -M.gammaTwo i j := by
    unfold AlgebraData.gammaTwo
    module
  rw [hb, hg]
  simp only [Matrix.neg_apply]
  ring

/-- No original diagonal term survives because gammaTwo(i,i)=0. -/
theorem sourceOrderedCoefficient_diagonal_zero
    {N : ℕ} (M : AlgebraData N) (x : Boson N)
    (α β : SpinIndex) (A : ColorIndex N) (i : SpaceIndex) :
    M.coordinateBracketAll x i i A * M.gammaTwo i i α β = 0 := by
  simp [AlgebraData.gammaTwo]

/-- The full ordered-pair coefficient in the source original charge
matches the source upper-pair coefficient with its authentic 1/2 factor. -/
theorem sourceOriginalOrderedCoefficient_eq_upper
    {N : ℕ} (M : AlgebraData N) (x : Boson N)
    (α β : SpinIndex) (A : ColorIndex N) :
    (1 / 2 : ℝ) *
      (∑ i : SpaceIndex, ∑ j : SpaceIndex,
        M.coordinateBracketAll x i j A * M.gammaTwo i j α β) =
      ∑ p : BFSSGamma.SpatialPair,
        M.coordinateBracketAll x p.1.1 p.1.2 A *
          M.gammaTwo p.1.1 p.1.2 α β := by
  exact symmetricZeroDiagonal_halfDoubleSum_eq_upper
    (fun i j => M.coordinateBracketAll x i j A * M.gammaTwo i j α β)
    (sourceOrderedCoefficient_symmetric M x α β A)
    (sourceOrderedCoefficient_diagonal_zero M x α β A)

/-- The actual deformed source coefficient equals one-half of the full
original ordered-pair coefficient, with no assumed multiplier equality. -/
theorem sourceMasslessCoefficient_eq_halfOriginalOrdered
    {N : ℕ} (M : AlgebraData N) (x : Boson N)
    (α β : SpinIndex) (A : ColorIndex N) :
    M.deformedPotentialCoefficients 1 0 x α (β, A) =
      (1 / 2 : ℝ) *
        (∑ i : SpaceIndex, ∑ j : SpaceIndex,
          M.coordinateBracketAll x i j A * M.gammaTwo i j α β) := by
  rw [sourceMasslessCoefficient_eq_originalUpperTriangle]
  exact (sourceOriginalOrderedCoefficient_eq_upper M x α β A).symm

#print axioms symmetricZeroDiagonal_halfDoubleSum_eq_upper
#print axioms sourceOrderedCoefficient_symmetric
#print axioms sourceOrderedCoefficient_diagonal_zero
#print axioms sourceOriginalOrderedCoefficient_eq_upper
#print axioms sourceMasslessCoefficient_eq_halfOriginalOrdered

end
end FCP.BFSSSU2GaugeG4K9C
