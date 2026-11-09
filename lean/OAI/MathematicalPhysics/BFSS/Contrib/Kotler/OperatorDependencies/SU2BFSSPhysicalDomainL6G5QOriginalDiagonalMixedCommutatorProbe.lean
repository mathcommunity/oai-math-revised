import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5POriginalScalarMixedRemainderProbe

/-!
L6G5Q: original SU(2) diagonal kinetic/quadratic commutator.
For each original fermion label (beta,a), the actual kinetic
coefficient differentiates color a, while the quadratic position
coefficient has zero terms whenever either position color is a.
The proof uses the pinned Pauli constants and genuine SmoothCore
Heisenberg/Leibniz law, not assumed differential commutativity.

This only removes the diagonal commutator from the ordered scalar
mixed term. The remaining right-ordered first-order operator must
still be identified with orbital Gauss. Fermionic Gauss, full
Hamiltonian, gauge restriction, and spectrum remain unproved here.
-/

set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G5Q
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G4A
open FCP.BFSSSU2PhysicalDomainL6G4B
open FCP.BFSSSU2PhysicalDomainL6G5B
open FCP.BFSSSU2PhysicalDomainL6G5C
open FCP.BFSSSU2PhysicalDomainL6G5D
open FCP.BFSSSU2PhysicalDomainL6G5E
open FCP.BFSSSU2PhysicalDomainL6G5P

/-- Actual normalized-Pauli SU(2) bracket is zero when the first
two colors repeat; this is not an arbitrary AlgebraData premise. -/
theorem sourceSU2StructureConstant_repeatLeft_zero
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (a c : ColorIndex 2) :
    M.structureConstant a a c = 0 := by
  rw [FCP.BFSSSU2.algebraData_structureConstant_of_pauli_color M hcolor]
  fin_cases a <;> fin_cases c <;>
    simp [FCP.BFSSSU2.epsilon3]

/-- The analogous repeated last color vanishes. -/
theorem sourceSU2StructureConstant_repeatRight_zero
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (a b : ColorIndex 2) :
    M.structureConstant a b a = 0 := by
  rw [FCP.BFSSSU2.algebraData_structureConstant_of_pauli_color M hcolor]
  fin_cases a <;> fin_cases b <;>
    simp [FCP.BFSSSU2.epsilon3]

private theorem sourceQuadraticWeight_sameColor_left
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (α : SpinIndex) (p : FermionLabel 2)
    (v t : BosonLabel 2) (hv : v.2 = p.2) :
    sourceQuadraticWeight M α p v t = 0 := by
  unfold sourceQuadraticWeight
  rw [hv, sourceSU2StructureConstant_repeatLeft_zero M hcolor p.2 t.2]
  simp

private theorem sourceQuadraticWeight_sameColor_right
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (α : SpinIndex) (p : FermionLabel 2)
    (v t : BosonLabel 2) (ht : t.2 = p.2) :
    sourceQuadraticWeight M α p v t = 0 := by
  unfold sourceQuadraticWeight
  rw [ht, sourceSU2StructureConstant_repeatRight_zero M hcolor p.2 v.2]
  simp

/-- Every literal differential/position-pair response summand
vanishes: either the kinetic color selector is zero, or the
quadratic coefficient is zero, or the derivative label differs
from both position labels. -/
theorem sourceSU2WeightedPairResponse_zero
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (w : SpinIndex → ℝ) (α : SpinIndex)
    (p : FermionLabel 2) (u v t : BosonLabel 2) :
    (sourceSpinorKineticWeight M w p u *
      sourceQuadraticWeight M α p v t) •
        sourcePositionPairResponse u v t = 0 := by
  classical
  by_cases hu : u.2 = p.2
  · by_cases hv : v.2 = p.2
    · have hq := sourceQuadraticWeight_sameColor_left M hcolor α p v t hv
      simp [hq]
    · by_cases ht : t.2 = p.2
      · have hq := sourceQuadraticWeight_sameColor_right M hcolor α p v t ht
        simp [hq]
      · have huv : u ≠ v := by
          intro heq
          apply hv
          have hc : v.2 = u.2 :=
            congrArg (fun z : BosonLabel 2 => z.2) heq.symm
          exact hc.trans hu
        have hut : u ≠ t := by
          intro heq
          apply ht
          have hc : t.2 = u.2 :=
            congrArg (fun z : BosonLabel 2 => z.2) heq.symm
          exact hc.trans hu
        have hr : sourcePositionPairResponse u v t = 0 := by
          simp [sourcePositionPairResponse, huv, hut]
        simp [hr]
  · have hk : sourceSpinorKineticWeight M w p u = 0 := by
      unfold sourceSpinorKineticWeight sourceKineticWeight
      simp [hu]
    simp [hk]

private theorem opComm_sum_left
    {R I : Type*} [Ring R] [Fintype I] (F : I → R) (A : R) :
    opComm (∑ i, F i) A = ∑ i, opComm (F i) A := by
  simp only [opComm, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_sub_distrib]

private theorem opComm_sum_right
    {R I : Type*} [Ring R] [Fintype I] (A : R) (F : I → R) :
    opComm A (∑ i, F i) = ∑ i, opComm A (F i) := by
  simp only [opComm, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_sub_distrib]

private theorem opComm_smul_left
    {R : Type*} [Ring R] [Algebra ℂ R] (c : ℂ) (A B : R) :
    opComm (c • A) B = c • opComm A B := by
  simp only [opComm, smul_mul_assoc, mul_smul_comm, smul_sub]

private theorem opComm_smul_right
    {R : Type*} [Ring R] [Algebra ℂ R] (c : ℂ) (A B : R) :
    opComm A (c • B) = c • opComm A B := by
  simp only [opComm, smul_mul_assoc, mul_smul_comm, smul_sub]

private theorem sourceDiagonalComm_atom_zero
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (w : SpinIndex → ℝ) (α : SpinIndex)
    (p : FermionLabel 2) (u v t : BosonLabel 2) :
    opComm
      (sourceSpinorKineticWeight M w p u • sourceD u)
      (sourceQuadraticWeight M α p v t •
        (sourceP v * sourceP t)) = 0 := by
  have hpair : opComm (sourceD u) (sourceP v * sourceP t) =
      sourcePositionPairResponse u v t :=
    sourceD_positionPair_comm u v t
  calc
    _ = (sourceSpinorKineticWeight M w p u *
        sourceQuadraticWeight M α p v t) •
          sourcePositionPairResponse u v t := by
            rw [opComm_smul_left, opComm_smul_right, hpair]
            rw [smul_smul]
    _ = 0 := sourceSU2WeightedPairResponse_zero M hcolor w α p u v t

/-- Literal source kinetic coefficient and its same-label quadratic
multiplication have zero commutator on the genuine SmoothCore.
No gamma hypothesis is required. -/
theorem sourceSpinorKineticQuadratic_comm_zero
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (w : SpinIndex → ℝ) (p : FermionLabel 2) :
    sourceSpinorKineticDifferential M w p *
        sourceSpinorQuadraticMultiplication M w p -
      sourceSpinorQuadraticMultiplication M w p *
        sourceSpinorKineticDifferential M w p = 0 := by
  classical
  change opComm (sourceSpinorKineticDifferential M w p)
    (sourceSpinorQuadraticMultiplication M w p) = 0
  rw [sourceSpinorKineticDifferential, sourceSpinorQuadraticMultiplication]
  rw [opComm_sum_left]
  apply Finset.sum_eq_zero
  intro u _
  rw [opComm_sum_right]
  apply Finset.sum_eq_zero
  intro α _
  rw [opComm_smul_right]
  rw [opComm_sum_right, Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro v _
  rw [opComm_sum_right, Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro t _
  rw [sourceDiagonalComm_atom_zero M hcolor w α p u v t]
  exact smul_zero _

/-- Every same-label commutator vanishes separately, so their
original fermion-label sum is zero. -/
theorem sourceSpinorMixedCommutator_zero
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (w : SpinIndex → ℝ) :
    sourceSpinorMixedCommutator M w = 0 := by
  unfold sourceSpinorMixedCommutator
  apply Finset.sum_eq_zero
  intro p _
  exact sourceSpinorKineticQuadratic_comm_zero M hcolor w p

/-- The exact original ordered kinetic/quadratic scalar cross-term
is twice the RIGHT-ordered term. This is still a first-order
operator, NOT yet orbital Gauss nor a zero operator. -/
theorem sourceSpinorOrderedMixedTerm_eq_rightOrdered
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (w : SpinIndex → ℝ) :
    sourceSpinorOrderedMixedTerm M w =
      (2 : ℂ) • sourceSpinorRightOrderedMixed M w := by
  rw [sourceSpinorOrderedMixedTerm_split,
      sourceSpinorMixedCommutator_zero M hcolor w]
  simp

#print axioms sourceSU2StructureConstant_repeatLeft_zero
#print axioms sourceSU2StructureConstant_repeatRight_zero
#print axioms sourceSU2WeightedPairResponse_zero
#print axioms sourceSpinorKineticQuadratic_comm_zero
#print axioms sourceSpinorMixedCommutator_zero
#print axioms sourceSpinorOrderedMixedTerm_eq_rightOrdered
#check @sourceSpinorOrderedMixedTerm_eq_rightOrdered
end
end FCP.BFSSSU2PhysicalDomainL6G5Q
