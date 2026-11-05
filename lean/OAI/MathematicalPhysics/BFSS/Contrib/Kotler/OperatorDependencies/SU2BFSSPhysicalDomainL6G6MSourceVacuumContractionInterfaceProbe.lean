import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6LOriginalInfinitesimalColorActionProbe

/-!
L6G6M — precise finite spin-pair vacuum contraction interface.

The original source bounded color generator annihilates a fiber vector
provided the *off-diagonal* color pairs cancel after summation over
the original 16 spin labels. This is a condition to be discharged from
the exact paired 24-mode Fock Majoranas; it is NOT assumed as a
property of the original representation.

The finite-sum rearrangement is proved abstractly, without expanding
the 2^24-dimensional Hilbert space or changing the source operator.
This gate does not assert the actual paired Fock vacuum satisfies the
condition: that is the next distinct source-facing obligation.
-/

set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G6M
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open FCP.BFSSSU2PhysicalDomainL6G6K

/-- Contract an abstract color-skew coefficient against spin-pair
vectors: a diagonal-zero coefficient and an off-diagonal-zero spin
sum force the full triple contraction to vanish. -/
private theorem finiteDiagonalZeroVacuumContraction
    {S C V : Type*}
    [Fintype S] [Fintype C] [DecidableEq C]
    [AddCommMonoid V] [Module ℂ V]
    (F : C → C → ℂ) (hdiag : ∀ a, F a a = 0)
    (X : S → C → C → V)
    (hoff : ∀ a b, a ≠ b → (∑ s : S, X s a b) = 0) :
    (∑ s : S, ∑ a : C, ∑ b : C, F a b • X s a b) = 0 := by
  classical
  calc
    _ = ∑ a : C, ∑ b : C, F a b • (∑ s : S, X s a b) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      simp only [Finset.smul_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro b _
      by_cases hab : a = b
      · subst b
        simp only [hdiag, zero_smul]
      · rw [hoff a b hab, smul_zero]

/-- Concrete, falsifiable source interface: the *literal* original
bounded J_F=iG_F kills Ω if the same source Majoranas obey the
off-diagonal spin-pair vacuum cancellation. No external gauge
representation or unproved vacuum assertion is used. -/
theorem sourceFiberFermionColorGenerator_vacuum_of_pairCancellation
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (c : ColorIndex 2) (Ω : Fermion 2)
    (hpair : ∀ a b : ColorIndex 2, a ≠ b →
      (∑ s : SpinIndex, (M.theta s a * M.theta s b) Ω) = 0) :
    sourceFiberFermionColorGenerator M c Ω = 0 := by
  classical
  have hdiag (a : ColorIndex 2) :
      (M.structureConstant a a c : ℂ) = 0 := by
    have hs := FCP.BFSSSU2PhysicalDomainL6G6D.sourceSU2StructureConstant_swapFirst
      M hcolor a a c
    have hz : M.structureConstant a a c = 0 := by
      linarith only [hs]
    exact_mod_cast hz
  have hsum :
      (∑ s : SpinIndex, ∑ a : ColorIndex 2,
        ∑ b : ColorIndex 2,
        (M.structureConstant a b c : ℂ) •
          (M.theta s a (M.theta s b Ω))) = 0 :=
    finiteDiagonalZeroVacuumContraction
      (fun a b => (M.structureConstant a b c : ℂ))
      hdiag (fun s a b => M.theta s a (M.theta s b Ω))
      (by
        intro a b hab
        simpa only [_root_.mul_apply_eq_comp] using
          (hpair a b hab))
  have hv :
      (∑ s : SpinIndex, ∑ a : ColorIndex 2,
        ∑ b : ColorIndex 2,
        sourceFiberFermionColorTerm M c s a b) Ω = 0 := by
    simpa only [_root_.sum_apply,
      sourceFiberFermionColorTerm, _root_.smul_apply,
      _root_.mul_apply_eq_comp] using hsum
  change
    (Complex.I • ((-Complex.I / 2 : ℂ) •
      (∑ s : SpinIndex, ∑ a : ColorIndex 2,
        ∑ b : ColorIndex 2, sourceFiberFermionColorTerm M c s a b))) Ω = 0
  simp only [_root_.smul_apply, hv, smul_zero]

#print axioms finiteDiagonalZeroVacuumContraction
#print axioms sourceFiberFermionColorGenerator_vacuum_of_pairCancellation
#check @sourceFiberFermionColorGenerator_vacuum_of_pairCancellation

end
end FCP.BFSSSU2PhysicalDomainL6G6M
