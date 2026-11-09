import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5LSourcePauliCyclicCoefficientProbe

/-!
L6G5M — prove the ORIGINAL SU(2) bosonic fixed-color bracket norm
is precisely the Lagrange area of its two cyclic color vectors.
The proof uses the source Pauli basis normalization and a universal
finite wedge-square/Lagrange identity. This is the color counterpart
of the qualified gamma spinor-row Gram, not their final contraction.
-/
set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G5M
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G5L

/-- Genuine finite-index Lagrange identity. It proves explicitly that
the antisymmetric color four-index contribution has the wedge norm
required by the original nine-space source potential. -/
theorem finiteWedge_lagrange
    {I : Type*} [Fintype I] (u v : I → ℝ) :
    (1 / 2 : ℝ) * (∑ i : I, ∑ j : I,
        (u i * v j - u j * v i) ^ 2) =
      ((∑ i : I, u i ^ 2) * (∑ i : I, v i ^ 2)) -
        (∑ i : I, u i * v i) ^ 2 := by
  classical
  have hprod :
      (∑ i : I, ∑ j : I, (u i * v j) ^ 2) =
        (∑ i : I, u i ^ 2) * (∑ j : I, v j ^ 2) := by
    calc
      _ = ∑ i : I, ∑ j : I, u i ^ 2 * v j ^ 2 := by
            simp only [mul_pow]
      _ = _ := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
  have hswap :
      (∑ i : I, ∑ j : I, (u j * v i) ^ 2) =
        (∑ i : I, ∑ j : I, (u i * v j) ^ 2) := by
    rw [Finset.sum_comm]
  have hcross :
      (∑ i : I, ∑ j : I, (u i * v j) * (u j * v i)) =
        (∑ i : I, u i * v i) ^ 2 := by
    calc
      _ = ∑ i : I, ∑ j : I, (u i * v i) * (u j * v j) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = (∑ i : I, u i * v i) * (∑ j : I, u j * v j) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
      _ = _ := by rw [pow_two]
  calc
    (1 / 2 : ℝ) * ∑ i : I, ∑ j : I,
        (u i * v j - u j * v i) ^ 2 =
      (1 / 2 : ℝ) *
        ((∑ i : I, ∑ j : I, (u i * v j) ^ 2) +
         (∑ i : I, ∑ j : I, (u j * v i) ^ 2) -
         2 * (∑ i : I, ∑ j : I,
           (u i * v j) * (u j * v i))) := by
             have hterm (i j : I) :
                 (u i * v j - u j * v i) ^ 2 =
                   (u i * v j) ^ 2 + (u j * v i) ^ 2 -
                     2 * ((u i * v j) * (u j * v i)) := by ring
             simp_rw [hterm]
             simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
               ← Finset.mul_sum]
    _ = _ := by rw [hprod, hswap, hprod, hcross]; ring

/-- Per ORIGINAL Pauli-source color, the full ordered nine-space
bracket-square target equals the Gram determinant of its true two
complementary color coordinate vectors. -/
theorem sourceSU2ColorBracketEnergy_area
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (x : Boson 2) (a : ColorIndex 2) :
    (1 / 4 : ℝ) * (∑ i : SpaceIndex, ∑ j : SpaceIndex,
      (M.coordinateBracketAll x i j a) ^ 2) =
      ((∑ i : SpaceIndex, (sourceCyclicU x a i) ^ 2) *
       (∑ i : SpaceIndex, (sourceCyclicV x a i) ^ 2)) -
      (∑ i : SpaceIndex,
        sourceCyclicU x a i * sourceCyclicV x a i) ^ 2 := by
  let u := sourceCyclicU x a
  let v := sourceCyclicV x a
  have hb (i j : SpaceIndex) :
      M.coordinateBracketAll x i j a =
        Real.sqrt 2 * (u i * v j - u j * v i) :=
    sourceSU2Bracket_eq_cyclicWedge M hcolor x a i j
  calc
    (1 / 4 : ℝ) * ∑ i : SpaceIndex, ∑ j : SpaceIndex,
        (M.coordinateBracketAll x i j a) ^ 2 =
      (1 / 2 : ℝ) * ∑ i : SpaceIndex, ∑ j : SpaceIndex,
        (u i * v j - u j * v i) ^ 2 := by
          simp_rw [hb]
          simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          simp only [← Finset.mul_sum]
          ring
    _ = _ := finiteWedge_lagrange u v

#print axioms finiteWedge_lagrange
#print axioms sourceSU2ColorBracketEnergy_area
#check @sourceSU2ColorBracketEnergy_area
end
end FCP.BFSSSU2PhysicalDomainL6G5M
