import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6AOriginalFermionicResponsePointwiseProbe

/-!
L6G6B — signed original real-spinor row Fierz identity contracted with
the genuine source structure constants and bosonic coordinates.

This stage uses the already-accepted original arbitrary-real-spinor
Fierz theorem. The output explicitly separates the scalar multiple of
the ORIGINAL source gamma matrix (fermionic potential channel) from the
Kronecker spinor trace (fermionic Gauss channel). Source f_{abc}, the
original gammaTwo, and the original bosonic coordinates stay unchanged.

It is a finite scalar coefficient theorem. The further identification
with G6A's full commutator response and the ordered Majorana contraction
is NOT asserted here; neither is a spectral/domain conclusion.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G6B
noncomputable section
open scoped Matrix BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G1
open FCP.BFSSSU2PhysicalDomainL6G2
open FCP.BFSSSU2PhysicalDomainL6G3

/-- The original gammaTwo and the signed ROW contraction coincide
with the accepted generalized source Fierz theorem. Valid for ALL w,
not merely unit spinors or basis vectors. -/
theorem sourceOriginalFermionFierz_row
    {N : ℕ} (M : AlgebraData N)
    (hgamma : M.gamma = originalGamma)
    (w : SpinIndex → ℝ) (k : SpaceIndex) (r s : SpinIndex) :
    (∑ i : SpaceIndex,
      ((w ᵥ* M.gamma i) r * (w ᵥ* M.gammaTwo i k) s +
       (w ᵥ* M.gamma i) s * (w ᵥ* M.gammaTwo i k) r)) =
      spinorSquareNorm w * M.gamma k r s -
        (if r = s then dotProduct w (M.gamma k *ᵥ w) else 0) := by
  change (∑ i : SpaceIndex,
      ((w ᵥ* M.gamma i) r *
        (w ᵥ* OAI.BFSSGamma.gammaTwo M.gamma i k) s +
        (w ᵥ* M.gamma i) s *
        (w ᵥ* OAI.BFSSGamma.gammaTwo M.gamma i k) r)) =
      spinorSquareNorm w * M.gamma k r s -
        (if r = s then dotProduct w (M.gamma k *ᵥ w) else 0)
  rw [hgamma]
  exact originalGamma_generalizedRowFierz w k r s

/-- Ordinary finite linearity that SEPARATES the source gamma and
Kronecker-trace contributions, without a gamma or color assumption. -/
private theorem finiteFierzChannels
    {C K : Type*} [Fintype C] [Fintype K]
    (a : C → K → ℝ) (g v : K → ℝ) (c : ℝ)
    (flag : Prop) [Decidable flag] :
    (∑ b : C, ∑ k : K,
      a b k * (c * g k - (if flag then v k else 0))) =
    c * (∑ b : C, ∑ k : K, a b k * g k) -
      (if flag then ∑ b : C, ∑ k : K, a b k * v k else 0) := by
  classical
  by_cases hf : flag
  · simp only [_root_.ite_eq_left hf]
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    simp only [mul_left_comm, mul_assoc]
  · simp only [_root_.ite_eq_right hf, sub_zero]
    simp only [Finset.mul_sum]
    simp only [mul_left_comm, mul_assoc]

/-- Signed original finite Fierz coefficient WITH the unchanged source
f_{abc} and x_{k,c}: the first term is precisely the gamma potential
coefficient, the second the diagonal fermionic Gauss coefficient.

The choice of the last color index c is retained literally. The next
gate must identify this finite coefficient with the G6A commutator
coefficient and then compose with ordered original theta pairs. -/
theorem sourceOriginalFermionFierz_colorChannels
    {N : ℕ} (M : AlgebraData N)
    (hgamma : M.gamma = originalGamma)
    (w : SpinIndex → ℝ) (x : Boson N)
    (a b : ColorIndex N) (r s : SpinIndex) :
    (∑ c : ColorIndex N, ∑ k : SpaceIndex,
      (M.structureConstant a b c * x (k,c)) *
        (∑ i : SpaceIndex,
          ((w ᵥ* M.gamma i) r * (w ᵥ* M.gammaTwo i k) s +
           (w ᵥ* M.gamma i) s * (w ᵥ* M.gammaTwo i k) r))) =
      spinorSquareNorm w *
        (∑ c : ColorIndex N, ∑ k : SpaceIndex,
          (M.structureConstant a b c * x (k,c)) * M.gamma k r s) -
      (if r = s then
        (∑ c : ColorIndex N, ∑ k : SpaceIndex,
          (M.structureConstant a b c * x (k,c)) *
            dotProduct w (M.gamma k *ᵥ w))
       else 0) := by
  calc
    _ = ∑ c : ColorIndex N, ∑ k : SpaceIndex,
      (M.structureConstant a b c * x (k,c)) *
        (spinorSquareNorm w * M.gamma k r s -
          (if r = s then dotProduct w (M.gamma k *ᵥ w) else 0)) := by
            apply Finset.sum_congr rfl
            intro c _
            apply Finset.sum_congr rfl
            intro k _
            rw [sourceOriginalFermionFierz_row M hgamma w k r s]
    _ = _ := finiteFierzChannels (C := ColorIndex N) (K := SpaceIndex)
        (fun c k => M.structureConstant a b c * x (k,c))
        (fun k => M.gamma k r s)
        (fun k => dotProduct w (M.gamma k *ᵥ w))
        (spinorSquareNorm w) (r = s)

#print axioms sourceOriginalFermionFierz_row
#print axioms finiteFierzChannels
#print axioms sourceOriginalFermionFierz_colorChannels
#check @sourceOriginalFermionFierz_colorChannels

end
end FCP.BFSSSU2PhysicalDomainL6G6B
