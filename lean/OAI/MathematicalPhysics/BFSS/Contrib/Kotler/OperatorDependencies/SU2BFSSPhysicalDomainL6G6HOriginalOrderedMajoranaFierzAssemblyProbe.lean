import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6GOriginalFermionFullFierzCoefficientProbe

/-!
L6G6H — ACTUAL original ordered Majorana response on SmoothCore.

This gate substitutes the kernel-qualified L6G6G signed Fierz
coefficient into the ORIGINAL L6G4B normal-ordered fermionic term.
Both theta operators remain in precisely their original order;
their genuine source CAR normalization is unchanged. The source
fermion action is used on its original fermion-valued smooth core,
not replaced by an abstract noncommutative algebra.

This is an exact operator-to-pointwise assembly of the complete
fermionic response, NOT an identification with the separately
defined fermionic Gauss generator or bosonic potential. The latter
normalization and full supercharge-square remain subsequent goals.
-/

set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G6H
noncomputable section
open scoped Matrix BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G1
open FCP.BFSSSU2PhysicalDomainL6G2
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G4A
open FCP.BFSSSU2PhysicalDomainL6G4B
open FCP.BFSSSU2PhysicalDomainL6G6A
open FCP.BFSSSU2PhysicalDomainL6G6G

/-- The literal accepted G6G real gamma and trace coefficient;
no derivative or redefined theta contribution. -/
def sourceFierzChannelsReal (M : AlgebraData 2)
    (w : SpinIndex → ℝ) (p q : FermionLabel 2)
    (x : Boson 2) : ℝ :=
  spinorSquareNorm w *
    (∑ c : ColorIndex 2, ∑ k : SpaceIndex,
      (M.structureConstant p.2 q.2 c * x (k,c)) *
        M.gamma k p.1 q.1) -
  (if p.1 = q.1 then
    (∑ c : ColorIndex 2, ∑ k : SpaceIndex,
      (M.structureConstant p.2 q.2 c * x (k,c)) *
        dotProduct w (M.gamma k *ᵥ w))
   else 0)

/-- The original ordered pair theta_p theta_q acting on its
actual core has exactly the previously proved signed
coefficient. The order of the two theta actions is NOT changed. -/
theorem sourceOriginalOrderedThetaPair_response_apply
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (hgamma : M.gamma = originalGamma)
    (w : SpinIndex → ℝ) (p q : FermionLabel 2)
    (f : SmoothCore 2) (x : Boson 2) :
    (((M.fermionAction p.1 p.2 * M.fermionAction q.1 q.2) *
        sourceAllSpinorCoefficientResponse M w p q) f) x =
      (Complex.I * (sourceFierzChannelsReal M w p q x : ℂ)) •
        (M.theta p.1 p.2 (M.theta q.1 q.2 (f x))) := by
  change M.theta p.1 p.2
    (M.theta q.1 q.2
      (((sourceAllSpinorCoefficientResponse M w p q) f) x)) = _
  rw [sourceAllSpinorCoefficientResponse_apply]
  rw [sourceAllSpinorResponsePoint_eq_fierzChannels M hcolor hgamma]
  change M.theta p.1 p.2
    (M.theta q.1 q.2
      ((Complex.I * (sourceFierzChannelsReal M w p q x : ℂ)) • f x)) = _
  simp only [map_smul]

/-- The EXACT source normal-ordered fermionic commutator term,
including its CAR factor 1/2 and the original theta order. -/
def sourceOriginalOrderedFermionicResponse
    (M : AlgebraData 2) (w : SpinIndex → ℝ) : SourceEnd 2 :=
  (1 / 2 : ℂ) •
    (∑ p : FermionLabel 2, ∑ q : FermionLabel 2,
      (M.fermionAction p.1 p.2 * M.fermionAction q.1 q.2) *
        sourceAllSpinorCoefficientResponse M w p q)

/-- Evaluation on the true SmoothCore is linear in the source
endomorphism. This avoids expanding the concrete Fock realization
or recomputing any of its Clifford products. -/
private def evalOriginalFermionEnd
    (f : SmoothCore 2) (x : Boson 2) :
    SourceEnd 2 →ₗ[ℂ] Fermion 2 where
  toFun T := (T f) x
  map_add' A B := by rfl
  map_smul' c A := by rfl

/-- Full ordered original theta response, with no replacement CAR
operators or assumed identification of the two output channels. -/
theorem sourceOriginalOrderedFermionicResponse_apply
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (hgamma : M.gamma = originalGamma)
    (w : SpinIndex → ℝ)
    (f : SmoothCore 2) (x : Boson 2) :
    ((sourceOriginalOrderedFermionicResponse M w) f) x =
      (1 / 2 : ℂ) •
        (∑ p : FermionLabel 2, ∑ q : FermionLabel 2,
          (Complex.I * (sourceFierzChannelsReal M w p q x : ℂ)) •
            (M.theta p.1 p.2 (M.theta q.1 q.2 (f x)))) := by
  change (evalOriginalFermionEnd f x)
    (sourceOriginalOrderedFermionicResponse M w) = _
  unfold sourceOriginalOrderedFermionicResponse
  rw [map_smul]
  simp only [map_sum]
  apply congrArg (fun v : Fermion 2 => (1 / 2 : ℂ) • v)
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  exact sourceOriginalOrderedThetaPair_response_apply
    M hcolor hgamma w p q f x

#print axioms sourceOriginalOrderedThetaPair_response_apply
#print axioms sourceOriginalOrderedFermionicResponse_apply
#check @sourceOriginalOrderedFermionicResponse_apply

end
end FCP.BFSSSU2PhysicalDomainL6G6H
