import OAI.MathematicalPhysics.BFSS.Core

/-!
# L6G3 — CAR normal ordering of the literal original smooth-core charge

The coefficient operators below only regroup the pinned original kinetic
and quadratic-position summands. They use the original SmoothCore, theta,
gamma, structureConstant, coordinateDerivative and position definitions.

All fermion/coefficient commutation premises are discharged from Core's
source theorems. The CAR is lifted from AlgebraData.theta_CAR. No concrete
Fock representation is expanded, and no Gauss or spectral identity is
assumed. Identifying the scalar and commutator terms with H0 and BOTH
parts of the Gauss generator is a subsequent obligation.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G3
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData

abbrev SourceEnd (N : ℕ) := Module.End ℂ (SmoothCore N)
abbrev FermionLabel (N : ℕ) := SpinIndex × ColorIndex N

/-- Exact scalar differential coefficient of one original fermion label. -/
def sourceCoefficient {N : ℕ} (M : AlgebraData N)
    (α : SpinIndex) (p : FermionLabel N) : SourceEnd N :=
  (∑ i : SpaceIndex, (-Complex.I * (M.gamma i α p.1 : ℂ)) •
    coordinateDerivative i p.2) +
  ∑ i : SpaceIndex, ∑ j : SpaceIndex,
    ∑ B : ColorIndex N, ∑ C : ColorIndex N,
    (((1 / 2 : ℝ) * M.structureConstant p.2 B C *
      M.gammaTwo i j α p.1 : ℝ) : ℂ) • (position i B * position j C)

/-- The weighted charge is the actual finite sum of original charges. -/
def sourceAllSpinorCharge {N : ℕ} (M : AlgebraData N)
    (w : SpinIndex → ℝ) : SourceEnd N :=
  ∑ α : SpinIndex, (w α : ℂ) • M.charge α

def sourceAllSpinorCoefficient {N : ℕ} (M : AlgebraData N)
    (w : SpinIndex → ℝ) (p : FermionLabel N) : SourceEnd N :=
  ∑ α : SpinIndex, (w α : ℂ) • sourceCoefficient M α p

/-- Source delta-one CAR on the original smooth test core. -/
theorem sourceFermionAction_CAR {N : ℕ} (M : AlgebraData N)
    (p q : FermionLabel N) :
    M.fermionAction p.1 p.2 * M.fermionAction q.1 q.2 +
      M.fermionAction q.1 q.2 * M.fermionAction p.1 p.2 =
    if p = q then (1 : SourceEnd N) else 0 := by
  classical
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  change M.theta p.1 p.2 (M.theta q.1 q.2 (f x)) +
    M.theta q.1 q.2 (M.theta p.1 p.2 (f x)) =
      ((if p = q then (1 : SourceEnd N) else 0) f) x
  have h := congrArg (fun K : Fermion N →L[ℂ] Fermion N => K (f x))
    (M.theta_CAR p.1 q.1 p.2 q.2)
  by_cases hpq : p = q
  · subst q
    simp only [if_pos rfl]
    change M.theta p.1 p.2 (M.theta p.1 p.2 (f x)) +
      M.theta p.1 p.2 (M.theta p.1 p.2 (f x)) = f x
    simpa [ContinuousLinearMap.mul_apply] using h
  · have hpair : ¬ (p.1 = q.1 ∧ p.2 = q.2) :=
      fun h' => hpq (Prod.ext h'.1 h'.2)
    simp only [if_neg hpq]
    change M.theta p.1 p.2 (M.theta q.1 q.2 (f x)) +
      M.theta q.1 q.2 (M.theta p.1 p.2 (f x)) = 0
    simpa [hpair, ContinuousLinearMap.mul_apply] using h

private theorem sourcePositionProduct_comm_fermion {N : ℕ}
    (M : AlgebraData N) (q : FermionLabel N)
    (i j : SpaceIndex) (B C : ColorIndex N) :
    (position i B * position j C) * M.fermionAction q.1 q.2 =
      M.fermionAction q.1 q.2 * (position i B * position j C) := by
  have hi : M.fermionAction q.1 q.2 * position i B =
      position i B * M.fermionAction q.1 q.2 :=
    M.fermionAction_position_commute q.1 q.2 B i
  have hj : M.fermionAction q.1 q.2 * position j C =
      position j C * M.fermionAction q.1 q.2 :=
    M.fermionAction_position_commute q.1 q.2 C j
  calc
    _ = position i B * (position j C * M.fermionAction q.1 q.2) :=
      mul_assoc _ _ _
    _ = position i B * (M.fermionAction q.1 q.2 * position j C) := by rw [hj]
    _ = (position i B * M.fermionAction q.1 q.2) * position j C :=
      (mul_assoc _ _ _).symm
    _ = (M.fermionAction q.1 q.2 * position i B) * position j C := by rw [hi]
    _ = _ := mul_assoc _ _ _

/-- No assumed derivative, position, or fermion commutation law. -/
theorem sourceCoefficient_comm_fermion {N : ℕ} (M : AlgebraData N)
    (α : SpinIndex) (p q : FermionLabel N) :
    sourceCoefficient M α p * M.fermionAction q.1 q.2 =
      M.fermionAction q.1 q.2 * sourceCoefficient M α p := by
  unfold sourceCoefficient
  simp only [add_mul, mul_add, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm]
  apply congrArg₂ (fun A B : SourceEnd N => A + B)
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (M.fermionAction_derivative_commute q.1 q.2 p.2 i).symm
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro B _
    apply Finset.sum_congr rfl
    intro C _
    congr 1
    exact sourcePositionProduct_comm_fermion M q i j B C

private theorem kineticSum_labelsFirst {N : ℕ} {R : Type*}
    [AddCommMonoid R] (F : SpaceIndex → ColorIndex N → SpinIndex → R) :
    (∑ i : SpaceIndex, ∑ A : ColorIndex N, ∑ β : SpinIndex, F i A β) =
      ∑ β : SpinIndex, ∑ A : ColorIndex N, ∑ i : SpaceIndex, F i A β := by
  calc
    _ = ∑ A : ColorIndex N, ∑ i : SpaceIndex, ∑ β : SpinIndex, F i A β :=
      Finset.sum_comm
    _ = ∑ A : ColorIndex N, ∑ β : SpinIndex, ∑ i : SpaceIndex, F i A β := by
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

private theorem cubicSum_labelsFirst {N : ℕ} {R : Type*}
    [AddCommMonoid R]
    (F : SpaceIndex → SpaceIndex → ColorIndex N → ColorIndex N →
      ColorIndex N → SpinIndex → R) :
    (∑ i : SpaceIndex, ∑ j : SpaceIndex, ∑ A : ColorIndex N,
      ∑ B : ColorIndex N, ∑ C : ColorIndex N, ∑ β : SpinIndex, F i j A B C β) =
    ∑ β : SpinIndex, ∑ A : ColorIndex N, ∑ i : SpaceIndex,
      ∑ j : SpaceIndex, ∑ B : ColorIndex N, ∑ C : ColorIndex N, F i j A B C β := by
  calc
    _ = ∑ i : SpaceIndex, ∑ j : SpaceIndex, ∑ A : ColorIndex N,
      ∑ B : ColorIndex N, ∑ β : SpinIndex, ∑ C : ColorIndex N, F i j A B C β := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      rw [Finset.sum_comm]
    _ = ∑ i : SpaceIndex, ∑ j : SpaceIndex, ∑ A : ColorIndex N,
      ∑ β : SpinIndex, ∑ B : ColorIndex N, ∑ C : ColorIndex N, F i j A B C β := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.sum_comm]
    _ = ∑ i : SpaceIndex, ∑ j : SpaceIndex, ∑ β : SpinIndex,
      ∑ A : ColorIndex N, ∑ B : ColorIndex N, ∑ C : ColorIndex N, F i j A B C β := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ i : SpaceIndex, ∑ β : SpinIndex, ∑ j : SpaceIndex,
      ∑ A : ColorIndex N, ∑ B : ColorIndex N, ∑ C : ColorIndex N, F i j A B C β := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ β : SpinIndex, ∑ i : SpaceIndex, ∑ j : SpaceIndex,
      ∑ A : ColorIndex N, ∑ B : ColorIndex N, ∑ C : ColorIndex N, F i j A B C β :=
      Finset.sum_comm
    _ = ∑ β : SpinIndex, ∑ i : SpaceIndex, ∑ A : ColorIndex N,
      ∑ j : SpaceIndex, ∑ B : ColorIndex N, ∑ C : ColorIndex N, F i j A B C β := by
      apply Finset.sum_congr rfl
      intro β _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro β _
      rw [Finset.sum_comm]

/-- Literal original charge regrouping, preserving every source coefficient. -/
theorem sourceCharge_factorization {N : ℕ} (M : AlgebraData N) (α : SpinIndex) :
    M.charge α = ∑ p : FermionLabel N,
      M.fermionAction p.1 p.2 * sourceCoefficient M α p := by
  unfold charge
  simp only [Fintype.sum_prod_type, sourceCoefficient, mul_add,
    Finset.mul_sum, mul_smul_comm, Finset.sum_add_distrib]
  apply congrArg₂ (fun A B : SourceEnd N => A + B)
  · exact kineticSum_labelsFirst _
  · exact cubicSum_labelsFirst _

theorem sourceAllSpinorCharge_factorization {N : ℕ} (M : AlgebraData N)
    (w : SpinIndex → ℝ) :
    sourceAllSpinorCharge M w = ∑ p : FermionLabel N,
      M.fermionAction p.1 p.2 * sourceAllSpinorCoefficient M w p := by
  unfold sourceAllSpinorCharge sourceAllSpinorCoefficient
  simp only [sourceCharge_factorization, Finset.smul_sum,
    Finset.mul_sum, mul_smul_comm]
  exact Finset.sum_comm

theorem sourceAllSpinorCoefficient_comm_fermion {N : ℕ} (M : AlgebraData N)
    (w : SpinIndex → ℝ) (p q : FermionLabel N) :
    sourceAllSpinorCoefficient M w p * M.fermionAction q.1 q.2 =
      M.fermionAction q.1 q.2 * sourceAllSpinorCoefficient M w p := by
  unfold sourceAllSpinorCoefficient
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  apply Finset.sum_congr rfl
  intro α _
  exact congrArg (fun T : SourceEnd N => (w α : ℂ) • T)
    (sourceCoefficient_comm_fermion M α p q)

private theorem carPair {R I : Type*} [Ring R] [DecidableEq I]
    (θ L : I → R)
    (hCAR : ∀ p q, θ p * θ q + θ q * θ p = if p = q then 1 else 0)
    (hcomm : ∀ p q, L p * θ q = θ q * L p) (p q : I) :
    (θ p * L p) * (θ q * L q) + (θ q * L q) * (θ p * L p) =
      (if p = q then L p * L p else 0) +
        (θ p * θ q) * (L p * L q - L q * L p) := by
  have hterm (a b : I) : (θ a * L a) * (θ b * L b) =
      (θ a * θ b) * (L a * L b) := by
    calc
      _ = θ a * (L a * θ b) * L b := by noncomm_ring
      _ = _ := by rw [hcomm]; simp only [mul_assoc]
  rw [hterm p q, hterm q p]
  calc
    _ = (θ p * θ q + θ q * θ p) * (L q * L p) +
        (θ p * θ q) * (L p * L q - L q * L p) := by noncomm_ring
    _ = _ := by
      rw [hCAR]
      by_cases h : p = q
      · subst q
        simp
      · simp [h]

private theorem carNormalOrder {R I : Type*} [Ring R] [Algebra ℂ R]
    [Fintype I] [DecidableEq I] (θ L : I → R)
    (hCAR : ∀ p q, θ p * θ q + θ q * θ p = if p = q then 1 else 0)
    (hcomm : ∀ p q, L p * θ q = θ q * L p) :
    (∑ p, θ p * L p) * (∑ p, θ p * L p) =
      (1 / 2 : ℂ) • (∑ p, L p * L p) +
      (1 / 2 : ℂ) • (∑ p, ∑ q,
        (θ p * θ q) * (L p * L q - L q * L p)) := by
  let Q := ∑ p, θ p * L p
  have hdouble : Q * Q = ∑ p, ∑ q, (θ p * L p) * (θ q * L q) := by
    simp only [Q, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  have htwice : Q * Q + Q * Q = (∑ p, L p * L p) +
      ∑ p, ∑ q, (θ p * θ q) * (L p * L q - L q * L p) := by
    simp only [hdouble]
    conv_lhs => rhs; rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, carPair θ L hCAR hcomm]
    simp only [Finset.sum_add_distrib]
    simp
  calc
    Q * Q = (1 / 2 : ℂ) • (Q * Q + Q * Q) := by
      rw [smul_add, ← add_smul]
      norm_num
    _ = _ := by rw [htwice, smul_add]

/-- Full original smooth-core normal ordering of each source charge. -/
theorem sourceCharge_normalOrder {N : ℕ} (M : AlgebraData N) (α : SpinIndex) :
    M.charge α * M.charge α =
      (1 / 2 : ℂ) • (∑ p : FermionLabel N,
        sourceCoefficient M α p * sourceCoefficient M α p) +
      (1 / 2 : ℂ) • (∑ p : FermionLabel N, ∑ q : FermionLabel N,
        (M.fermionAction p.1 p.2 * M.fermionAction q.1 q.2) *
          (sourceCoefficient M α p * sourceCoefficient M α q -
            sourceCoefficient M α q * sourceCoefficient M α p)) := by
  classical
  simp only [sourceCharge_factorization]
  exact carNormalOrder (R := SourceEnd N) (I := FermionLabel N)
    (fun p : FermionLabel N => M.fermionAction p.1 p.2)
    (sourceCoefficient M α) (sourceFermionAction_CAR M)
    (sourceCoefficient_comm_fermion M α)

/-- All real spinors, including zero, with no CAR or commutation hypothesis. -/
theorem sourceAllSpinorCharge_normalOrder {N : ℕ} (M : AlgebraData N)
    (w : SpinIndex → ℝ) :
    sourceAllSpinorCharge M w * sourceAllSpinorCharge M w =
      (1 / 2 : ℂ) • (∑ p : FermionLabel N,
        sourceAllSpinorCoefficient M w p * sourceAllSpinorCoefficient M w p) +
      (1 / 2 : ℂ) • (∑ p : FermionLabel N, ∑ q : FermionLabel N,
        (M.fermionAction p.1 p.2 * M.fermionAction q.1 q.2) *
          (sourceAllSpinorCoefficient M w p * sourceAllSpinorCoefficient M w q -
            sourceAllSpinorCoefficient M w q * sourceAllSpinorCoefficient M w p)) := by
  classical
  simp only [sourceAllSpinorCharge_factorization]
  exact carNormalOrder (R := SourceEnd N) (I := FermionLabel N)
    (fun p : FermionLabel N => M.fermionAction p.1 p.2)
    (sourceAllSpinorCoefficient M w) (sourceFermionAction_CAR M)
    (sourceAllSpinorCoefficient_comm_fermion M w)

#print axioms sourceFermionAction_CAR
#print axioms sourceCoefficient_comm_fermion
#print axioms sourceCharge_factorization
#print axioms sourceAllSpinorCharge_factorization
#print axioms sourceAllSpinorCoefficient_comm_fermion
#print axioms carNormalOrder
#print axioms sourceCharge_normalOrder
#print axioms sourceAllSpinorCharge_normalOrder
#check @sourceAllSpinorCharge_normalOrder

end
end FCP.BFSSSU2PhysicalDomainL6G3
