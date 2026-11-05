import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G4AOriginalCoreCalculusProbe

/-!
# L6G4B — literal original coefficient commutator is linear multiplication

First prove finite polynomial differential algebra over an abstract ring.
Then discharge ALL derivative/position laws on the original source core,
and identify the polynomial with G3's unchanged original coefficient.
The final all-spinor result has no calculus, CAR or gauge premise.

The response retains original -i kinetic and 1/2 potential coefficients.
It contains only linear position multipliers. Contracting its fermion
labels into B and the fermionic Gauss generator is a subsequent gate.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G4B
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G4A

def opComm {R : Type*} [Ring R] (A B : R) : R := A * B - B * A

private theorem opComm_add_left {R : Type*} [Ring R] (A B C : R) :
    opComm (A + B) C = opComm A C + opComm B C := by
  unfold opComm
  noncomm_ring

private theorem opComm_add_right {R : Type*} [Ring R] (A B C : R) :
    opComm A (B + C) = opComm A B + opComm A C := by
  unfold opComm
  noncomm_ring

private theorem opComm_neg_swap {R : Type*} [Ring R] (A B : R) :
    opComm A B = -opComm B A := by
  unfold opComm
  abel

private theorem opComm_mul_left {R : Type*} [Ring R] (A B C : R) :
    opComm (A * B) C = A * opComm B C + opComm A C * B := by
  unfold opComm
  noncomm_ring

private theorem opComm_mul_right {R : Type*} [Ring R] (A B C : R) :
    opComm A (B * C) = opComm A B * C + B * opComm A C := by
  unfold opComm
  noncomm_ring

private theorem opComm_sum_left {R I : Type*} [Ring R] [Fintype I]
    (F : I → R) (A : R) :
    opComm (∑ i, F i) A = ∑ i, opComm (F i) A := by
  simp only [opComm, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]

private theorem opComm_sum_right {R I : Type*} [Ring R] [Fintype I]
    (A : R) (F : I → R) :
    opComm A (∑ i, F i) = ∑ i, opComm A (F i) := by
  simp only [opComm, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]

private theorem opComm_smul_smul {R : Type*} [Ring R] [Algebra ℂ R]
    (c d : ℂ) (A B : R) :
    opComm (c • A) (d • B) = (c * d) • opComm A B := by
  simp only [opComm, smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub]
  rw [mul_comm d c]

def differentialPolynomial {R I : Type*} [Ring R] [Algebra ℂ R] [Fintype I]
    (D P : I → R) (k : I → ℂ) (b : I → I → ℂ) : R :=
  (∑ u, k u • D u) + ∑ v, ∑ t, b v t • (P v * P t)

private theorem positionPair_comm {R I : Type*} [Ring R]
    (P : I → R) (hPP : ∀ u v, P u * P v = P v * P u) (u v t s : I) :
    opComm (P u * P v) (P t * P s) = 0 := by
  have h (a b : I) : opComm (P a) (P b) = 0 := by
    unfold opComm
    rw [hPP]
    exact sub_self _
  rw [opComm_mul_right, opComm_mul_left, opComm_mul_left]
  simp only [h, mul_zero, zero_mul, zero_add, add_zero]

private theorem differentialPolynomial_comm {R I : Type*}
    [Ring R] [Algebra ℂ R] [Fintype I]
    (D P : I → R) (response : I → I → I → R)
    (hDD : ∀ u v, D u * D v = D v * D u)
    (hPP : ∀ u v, P u * P v = P v * P u)
    (hDP : ∀ u v t, opComm (D u) (P v * P t) = response u v t)
    (k l : I → ℂ) (b c : I → I → ℂ) :
    opComm (differentialPolynomial D P k b) (differentialPolynomial D P l c) =
      ∑ u, ∑ v, ∑ t, (k u * c v t - l u * b v t) • response u v t := by
  have hK (a z : I → ℂ) :
      opComm (∑ u, a u • D u) (∑ v, z v • D v) = 0 := by
    simp_rw [opComm_sum_left, opComm_sum_right, opComm_smul_smul]
    have h (u v : I) : opComm (D u) (D v) = 0 := by
      unfold opComm
      rw [hDD]
      exact sub_self _
    simp only [h, smul_zero, Finset.sum_const_zero]
  have hW (a z : I → I → ℂ) :
      opComm (∑ u, ∑ v, a u v • (P u * P v))
        (∑ t, ∑ s, z t s • (P t * P s)) = 0 := by
    simp_rw [opComm_sum_left, opComm_sum_right, opComm_smul_smul,
      positionPair_comm P hPP]
    simp only [smul_zero, Finset.sum_const_zero]
  have hKW (a : I → ℂ) (z : I → I → ℂ) :
      opComm (∑ u, a u • D u) (∑ v, ∑ t, z v t • (P v * P t)) =
        ∑ u, ∑ v, ∑ t, (a u * z v t) • response u v t := by
    simp_rw [opComm_sum_left, opComm_sum_right, opComm_smul_smul, hDP]
  unfold differentialPolynomial
  rw [opComm_add_left, opComm_add_right, opComm_add_right, hK, hW]
  rw [opComm_neg_swap (∑ v, ∑ t, b v t • (P v * P t)) (∑ u, l u • D u)]
  rw [hKW, hKW]
  simp only [zero_add, add_zero, sub_smul,
    Finset.sum_sub_distrib]
  abel

/-- Original kinetic coefficient, with its genuine color selector. -/
def sourceKineticWeight {N : ℕ} (M : AlgebraData N)
    (α : SpinIndex) (p : FermionLabel N) (u : BosonLabel N) : ℂ :=
  if u.2 = p.2 then -Complex.I * (M.gamma u.1 α p.1 : ℂ) else 0

/-- Original ordered quadratic-position coefficient; no j<k renormalization. -/
def sourceQuadraticWeight {N : ℕ} (M : AlgebraData N)
    (α : SpinIndex) (p : FermionLabel N) (v t : BosonLabel N) : ℂ :=
  (((1 / 2 : ℝ) * M.structureConstant p.2 v.2 t.2 *
    M.gammaTwo v.1 t.1 α p.1 : ℝ) : ℂ)

/-- Identification with G3's unchanged scalar differential coefficient. -/
theorem sourceCoefficient_eq_polynomial {N : ℕ} (M : AlgebraData N)
    (α : SpinIndex) (p : FermionLabel N) :
    sourceCoefficient M α p = differentialPolynomial
      (sourceD (N := N)) (sourceP (N := N))
      (sourceKineticWeight M α p) (sourceQuadraticWeight M α p) := by
  classical
  unfold sourceCoefficient differentialPolynomial
  apply congrArg₂ (fun A B : SourceEnd N => A + B)
  · simp only [Fintype.sum_prod_type, sourceKineticWeight, sourceD]
    apply Finset.sum_congr rfl
    intro i _
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · simp only [Fintype.sum_prod_type, sourceQuadraticWeight, sourceP]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm

/-- The source response contains only linear original position multipliers. -/
def sourceCoefficientResponse {N : ℕ} (M : AlgebraData N)
    (α β : SpinIndex) (p q : FermionLabel N) : SourceEnd N :=
  ∑ u : BosonLabel N, ∑ v : BosonLabel N, ∑ t : BosonLabel N,
    (sourceKineticWeight M α p u * sourceQuadraticWeight M β q v t -
      sourceKineticWeight M β q u * sourceQuadraticWeight M α p v t) •
      sourcePositionPairResponse u v t

/-- Both source polynomials are identified, then ALL calculus laws discharged. -/
theorem sourceCoefficient_commutator {N : ℕ} (M : AlgebraData N)
    (α β : SpinIndex) (p q : FermionLabel N) :
    sourceCoefficient M α p * sourceCoefficient M β q -
      sourceCoefficient M β q * sourceCoefficient M α p =
        sourceCoefficientResponse M α β p q := by
  change opComm (sourceCoefficient M α p) (sourceCoefficient M β q) = _
  rw [sourceCoefficient_eq_polynomial, sourceCoefficient_eq_polynomial]
  exact differentialPolynomial_comm (R := SourceEnd N) (I := BosonLabel N)
    (sourceD (N := N)) (sourceP (N := N))
    (sourcePositionPairResponse (N := N)) sourceD_D_comm sourceP_P_comm
    sourceD_positionPair_comm
    (sourceKineticWeight M α p) (sourceKineticWeight M β q)
    (sourceQuadraticWeight M α p) (sourceQuadraticWeight M β q)

def sourceAllSpinorCoefficientResponse {N : ℕ} (M : AlgebraData N)
    (w : SpinIndex → ℝ) (p q : FermionLabel N) : SourceEnd N :=
  ∑ α : SpinIndex, ∑ β : SpinIndex,
    ((w α : ℂ) * (w β : ℂ)) • sourceCoefficientResponse M α β p q

/-- Literal all-real-spinor coefficient commutator; its RHS has no derivatives. -/
theorem sourceAllSpinorCoefficient_commutator {N : ℕ} (M : AlgebraData N)
    (w : SpinIndex → ℝ) (p q : FermionLabel N) :
    sourceAllSpinorCoefficient M w p * sourceAllSpinorCoefficient M w q -
      sourceAllSpinorCoefficient M w q * sourceAllSpinorCoefficient M w p =
        sourceAllSpinorCoefficientResponse M w p q := by
  change opComm (sourceAllSpinorCoefficient M w p)
    (sourceAllSpinorCoefficient M w q) = _
  unfold sourceAllSpinorCoefficient sourceAllSpinorCoefficientResponse
  simp_rw [opComm_sum_left, opComm_sum_right, opComm_smul_smul]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  exact congrArg (fun T : SourceEnd N => ((w α : ℂ) * (w β : ℂ)) • T)
    (sourceCoefficient_commutator M α β p q)

/-- Compose the new actual source response with the accepted G3 square. -/
theorem sourceAllSpinorCharge_normalOrder_response {N : ℕ} (M : AlgebraData N)
    (w : SpinIndex → ℝ) :
    sourceAllSpinorCharge M w * sourceAllSpinorCharge M w =
      (1 / 2 : ℂ) • (∑ p : FermionLabel N,
        sourceAllSpinorCoefficient M w p * sourceAllSpinorCoefficient M w p) +
      (1 / 2 : ℂ) • (∑ p : FermionLabel N, ∑ q : FermionLabel N,
        (M.fermionAction p.1 p.2 * M.fermionAction q.1 q.2) *
          sourceAllSpinorCoefficientResponse M w p q) := by
  rw [sourceAllSpinorCharge_normalOrder]
  simp only [sourceAllSpinorCoefficient_commutator]

#print axioms differentialPolynomial_comm
#print axioms sourceCoefficient_eq_polynomial
#print axioms sourceCoefficient_commutator
#print axioms sourceAllSpinorCoefficient_commutator
#print axioms sourceAllSpinorCharge_normalOrder_response
#check @sourceAllSpinorCoefficient_commutator
#check @sourceAllSpinorCharge_normalOrder_response

end
end FCP.BFSSSU2PhysicalDomainL6G4B
