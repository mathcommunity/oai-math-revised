import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6DOriginalFermionResponseSymmetricLegsProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5BOriginalComplexKineticColorGramProbe

/-!
L6G6E — the ORIGINAL all-spinor fermionic response polynomial is a
bilinear contraction of the genuine source kinetic and quadratic
coefficient weights.

Uses accepted G6D (the factor of two from BOTH source derivative
legs) and performs only finite scalar sum transport. In particular,
the original -i kinetic weight, ordered quadratic 1/2, spinor
weights, fermion color labels, and bosonic positions are unchanged.

This is the actual response-to-row bridge needed before the
signed G6B Fierz contraction. It does not yet assert Gauss,
the ordered theta-pair identity, or a physical-domain result.
-/

set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G6E
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G4A
open FCP.BFSSSU2PhysicalDomainL6G4B
open FCP.BFSSSU2PhysicalDomainL6G5B
open FCP.BFSSSU2PhysicalDomainL6G6A
open FCP.BFSSSU2PhysicalDomainL6G6D

/-- Exactly the original all-spinor quadratic coefficient for ONE
ordered pair of position labels, with no prematurely symmetrized sum. -/
def sourceSpinorQuadraticPairWeight
    (M : AlgebraData 2) (w : SpinIndex → ℝ)
    (p : FermionLabel 2) (u t : BosonLabel 2) : ℂ :=
  ∑ α : SpinIndex, (w α : ℂ) * sourceQuadraticWeight M α p u t

/-- Scalar finite bilinear contraction, retaining the relative
minus sign from the genuine source coefficient commutator. -/
private theorem finiteWeightedSpinorFactor
    {A : Type*} [Fintype A]
    (w K L Q R : A → ℂ) :
    (∑ α : A, ∑ β : A,
      (w α * w β) * (K α * Q β - L β * R α)) =
      (∑ α : A, w α * K α) * (∑ β : A, w β * Q β) -
      (∑ β : A, w β * L β) * (∑ α : A, w α * R α) := by
  have hprod (f g : A → ℂ) :
      (∑ α : A, ∑ β : A, f α * g β) =
        (∑ α : A, f α) * (∑ β : A, g β) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro α _
    rw [Finset.mul_sum]
  calc
    _ = (∑ α : A, ∑ β : A,
          ((w α * K α) * (w β * Q β) -
           (w α * R α) * (w β * L β))) := by
          apply Finset.sum_congr rfl
          intro α _
          apply Finset.sum_congr rfl
          intro β _
          ring
    _ = (∑ α : A, ∑ β : A, (w α * K α) * (w β * Q β)) -
        (∑ α : A, ∑ β : A, (w α * R α) * (w β * L β)) := by
          simp only [Finset.sum_sub_distrib]
    _ = (∑ α : A, w α * K α) * (∑ β : A, w β * Q β) -
        (∑ α : A, w α * R α) * (∑ β : A, w β * L β) := by
          rw [hprod (fun α => w α * K α) (fun β => w β * Q β),
              hprod (fun α => w α * R α) (fun β => w β * L β)]
    _ = _ := by ring

/-- Four-fold finite Fubini transport. It does not permute ANY
noncommuting operators: every term is a complex scalar. -/
private theorem finiteFourfoldResponseTranspose
    {A U T : Type*} [Fintype A] [Fintype U] [Fintype T]
    (F : A → A → U → T → ℂ) :
    (∑ α : A, ∑ β : A, ∑ u : U, ∑ t : T, F α β u t) =
      ∑ u : U, ∑ t : T, ∑ α : A, ∑ β : A, F α β u t := by
  calc
    _ = ∑ α : A, ∑ u : U, ∑ β : A, ∑ t : T, F α β u t := by
          apply Finset.sum_congr rfl
          intro α _
          exact Finset.sum_comm
    _ = ∑ u : U, ∑ α : A, ∑ β : A, ∑ t : T, F α β u t :=
      Finset.sum_comm
    _ = ∑ u : U, ∑ α : A, ∑ t : T, ∑ β : A, F α β u t := by
          apply Finset.sum_congr rfl
          intro u _
          apply Finset.sum_congr rfl
          intro α _
          exact Finset.sum_comm
    _ = _ := by
          apply Finset.sum_congr rfl
          intro u _
          exact Finset.sum_comm

/-- Contract BOTH original spinor indices against the actual -i
kinetic and 1/2 quadratic weights. The two channels remain
antisymmetric in the original fermion labels. -/
private theorem finiteWeightedResponseFactor
    {A U T : Type*} [Fintype A] [Fintype U] [Fintype T]
    (w : A → ℂ) (K L : A → U → ℂ)
    (Q R : A → U → T → ℂ) (x : T → ℂ) :
    (∑ α : A, ∑ β : A,
      (w α * w β) *
        (∑ u : U, ∑ t : T,
          (K α u * Q β u t - L β u * R α u t) * x t)) =
      ∑ u : U, ∑ t : T,
        ((∑ α : A, w α * K α u) * (∑ β : A, w β * Q β u t) -
         (∑ β : A, w β * L β u) * (∑ α : A, w α * R α u t)) * x t := by
  calc
    _ = ∑ α : A, ∑ β : A, ∑ u : U, ∑ t : T,
          (w α * w β) *
            ((K α u * Q β u t - L β u * R α u t) * x t) := by
              simp only [Finset.mul_sum]
    _ = ∑ u : U, ∑ t : T, ∑ α : A, ∑ β : A,
          (w α * w β) *
            ((K α u * Q β u t - L β u * R α u t) * x t) :=
      finiteFourfoldResponseTranspose _
    _ = ∑ u : U, ∑ t : T,
          (∑ α : A, ∑ β : A,
            (w α * w β) * (K α u * Q β u t - L β u * R α u t)) * x t := by
              apply Finset.sum_congr rfl
              intro u _
              apply Finset.sum_congr rfl
              intro t _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro α _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro β _
              ring
    _ = _ := by
          apply Finset.sum_congr rfl
          intro u _
          apply Finset.sum_congr rfl
          intro t _
          rw [finiteWeightedSpinorFactor
            w (fun α => K α u) (fun β => L β u)
              (fun β => Q β u t) (fun α => R α u t)]

/-- Main source-identified result: the accepted G6A ORIGINAL response
polynomial is twice the difference of two fully spinor-contracted,
UNMODIFIED source kinetic/quadratic pair products. -/
theorem sourceAllSpinorResponsePoint_eq_bilinear
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (w : SpinIndex → ℝ) (p q : FermionLabel 2)
    (x : Boson 2) :
    sourceAllSpinorResponsePoint M w p q x =
      (2 : ℂ) * (∑ u : BosonLabel 2, ∑ t : BosonLabel 2,
        (sourceSpinorKineticWeight M w p u *
           sourceSpinorQuadraticPairWeight M w q u t -
         sourceSpinorKineticWeight M w q u *
           sourceSpinorQuadraticPairWeight M w p u t) *
             ((x t : ℝ) : ℂ)) := by
  unfold sourceAllSpinorResponsePoint
  simp_rw [sourceCoefficientResponsePoint_eq_twice_first M hcolor]
  calc
    _ = (2 : ℂ) * (∑ α : SpinIndex, ∑ β : SpinIndex,
      ((w α : ℂ) * (w β : ℂ)) *
        sourceCoefficientResponseFirstLeg M α β p q x) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro α _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro β _
          ring
    _ = _ := by
          congr 1
          unfold sourceCoefficientResponseFirstLeg
            sourceSpinorKineticWeight sourceSpinorQuadraticPairWeight
          exact finiteWeightedResponseFactor
            (fun α : SpinIndex => (w α : ℂ))
            (fun α u => sourceKineticWeight M α p u)
            (fun β u => sourceKineticWeight M β q u)
            (fun β u t => sourceQuadraticWeight M β q u t)
            (fun α u t => sourceQuadraticWeight M α p u t)
            (fun t => ((x t : ℝ) : ℂ))

#print axioms finiteWeightedSpinorFactor
#print axioms finiteFourfoldResponseTranspose
#print axioms finiteWeightedResponseFactor
#print axioms sourceAllSpinorResponsePoint_eq_bilinear
#check @sourceAllSpinorResponsePoint_eq_bilinear

end
end FCP.BFSSSU2PhysicalDomainL6G6E
