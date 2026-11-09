import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6FOriginalFermionBilinearFierzKernelProbe

/-!
L6G6G — EXACT source fermionic response: signed Fierz contraction into
the original source gamma and diagonal fermionic Gauss coefficient.

Combines G6F's independently qualified ORIGINAL all-spinor pointwise
response equality with G6B's independently qualified real-spinor
color/Fierz identity. The finite transport is separately proved over
abstract finite sets before specializing to the 9x9x3 source indices.

This is the completed fixed-fermion-label SOURCE COEFFICIENT equality.
It is NOT an ordered theta-pair operator assembly or an assertion
about physical restriction, Hamiltonian spectrum, or mass gap.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G6G
noncomputable section
open scoped Matrix BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G1
open FCP.BFSSSU2PhysicalDomainL6G2
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G4A
open FCP.BFSSSU2PhysicalDomainL6G6A
open FCP.BFSSSU2PhysicalDomainL6G6B
open FCP.BFSSSU2PhysicalDomainL6G6F

/-- Exact change of finite sum order and scalar field: convert
a complex-cast triple sum to the real color-weighted spatial
Fierz sum. No sign, Clifford, gauge, or normal-ordering premise. -/
private theorem finiteRealFierzSumTransport
    {I K C : Type*} [Fintype I] [Fintype K] [Fintype C]
    (A : C → K → ℝ) (B : I → K → ℝ) :
    (∑ i : I, ∑ k : K, ∑ c : C,
      ((A c k : ℝ) : ℂ) * ((B i k : ℝ) : ℂ)) =
      (((∑ c : C, ∑ k : K,
        A c k * (∑ i : I, B i k)) : ℝ) : ℂ) := by
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  calc
    (∑ i : I, ∑ k : K, ∑ c : C,
      ((A c k : ℝ) : ℂ) * ((B i k : ℝ) : ℂ)) =
      ∑ k : K, ∑ i : I, ∑ c : C,
        ((A c k : ℝ) : ℂ) * ((B i k : ℝ) : ℂ) :=
          Finset.sum_comm
    _ = ∑ k : K, ∑ c : C, ∑ i : I,
          ((A c k : ℝ) : ℂ) * ((B i k : ℝ) : ℂ) := by
            apply Finset.sum_congr rfl
            intro k _
            exact Finset.sum_comm
    _ = ∑ c : C, ∑ k : K, ∑ i : I,
          ((A c k : ℝ) : ℂ) * ((B i k : ℝ) : ℂ) :=
            Finset.sum_comm

/-- Literal ORIGINAL SU(2) source point coefficient, for each pair
of real spinor/fermion labels. The exact +i factor and delta term
are derived from accepted source gamma/color/Fierz theorems.

The explicit Pauli-color identification and original-gamma
identification are retained as hypotheses, not silently assumed. -/
theorem sourceAllSpinorResponsePoint_eq_fierzChannels
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (hgamma : M.gamma = originalGamma)
    (w : SpinIndex → ℝ) (p q : FermionLabel 2)
    (x : Boson 2) :
    sourceAllSpinorResponsePoint M w p q x =
      Complex.I * (((spinorSquareNorm w *
        (∑ c : ColorIndex 2, ∑ k : SpaceIndex,
          (M.structureConstant p.2 q.2 c * x (k,c)) *
            M.gamma k p.1 q.1) -
        (if p.1 = q.1 then
          (∑ c : ColorIndex 2, ∑ k : SpaceIndex,
            (M.structureConstant p.2 q.2 c * x (k,c)) *
              dotProduct w (M.gamma k *ᵥ w))
         else 0)) : ℝ) : ℂ) := by
  rw [sourceAllSpinorResponsePoint_eq_originalRowKernel M hcolor hgamma]
  unfold sourceOriginalFermionRowKernel
  congr 1
  let A : ColorIndex 2 → SpaceIndex → ℝ :=
    fun c k => M.structureConstant p.2 q.2 c * x (k,c)
  let B : SpaceIndex → SpaceIndex → ℝ := fun i k =>
    ((w ᵥ* M.gamma i) p.1 * (w ᵥ* M.gammaTwo i k) q.1 +
     (w ᵥ* M.gamma i) q.1 * (w ᵥ* M.gammaTwo i k) p.1)
  calc
    (∑ i : SpaceIndex, ∑ k : SpaceIndex, ∑ c : ColorIndex 2,
       ((M.structureConstant p.2 q.2 c : ℂ) * ((x (k,c) : ℝ) : ℂ)) *
         (((((w ᵥ* M.gamma i) p.1 : ℝ) : ℂ) *
              (((w ᵥ* M.gammaTwo i k) q.1 : ℝ) : ℂ)) +
          ((((w ᵥ* M.gamma i) q.1 : ℝ) : ℂ) *
              (((w ᵥ* M.gammaTwo i k) p.1 : ℝ) : ℂ)))) =
      ∑ i : SpaceIndex, ∑ k : SpaceIndex, ∑ c : ColorIndex 2,
        ((A c k : ℝ) : ℂ) * ((B i k : ℝ) : ℂ) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro c _
          dsimp [A, B]
          simp only [Complex.ofReal_mul, Complex.ofReal_add]
    _ = (((∑ c : ColorIndex 2, ∑ k : SpaceIndex,
           A c k * (∑ i : SpaceIndex, B i k)) : ℝ) : ℂ) :=
             finiteRealFierzSumTransport A B
    _ = _ :=
      congrArg (fun z : ℝ => (z : ℂ))
        (sourceOriginalFermionFierz_colorChannels M hgamma w x
          p.2 q.2 p.1 q.1)

#print axioms finiteRealFierzSumTransport
#print axioms sourceAllSpinorResponsePoint_eq_fierzChannels
#check @sourceAllSpinorResponsePoint_eq_fierzChannels

end
end FCP.BFSSSU2PhysicalDomainL6G6G
