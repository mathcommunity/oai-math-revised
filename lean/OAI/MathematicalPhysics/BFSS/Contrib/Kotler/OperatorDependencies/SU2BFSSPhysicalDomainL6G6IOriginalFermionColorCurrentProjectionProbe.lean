import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6HOriginalOrderedMajoranaFierzAssemblyProbe

/-!
L6G6I — exact source fermionic color current and diagonal-spin
projector, with the original CAR normalization and theta order.

The accepted L6G6H ordered Majorana response has a Kronecker spin
trace channel. Here we identify its core operator content with the
source-built fermionic color-current candidate, preserving the
normal-ordered factor -i/2 and the original Pauli color structure
constants. The crucial diagonal contraction is proved on ABSTRACT
finite products before passing to BFSS.

This gate does not assert that the resulting color-current candidate
is the generator of the established fermionic gauge representation:
that is a separate covariance/infinitesimal action obligation.
Nor does it yet assemble the x-weighted potential or full Q square.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G6I
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G6H

/-- A universal diagonal-spin selector, which PRESERVES the order of
the other two indices and operates on arbitrary additive targets.
No CAR relation, spin dimension, or color assumption enters here. -/
private theorem finiteDiagonalSpinProjection
    {S C V : Type*} [Fintype S] [DecidableEq S] [Fintype C] [AddCommMonoid V]
    (F : S → C → C → V) :
    (∑ p : S × C, ∑ q : S × C,
      if p.1 = q.1 then F p.1 p.2 q.2 else 0) =
      ∑ s : S, ∑ a : C, ∑ b : C, F s a b := by
  classical
  simp only [Fintype.sum_prod_type]
  calc
    (∑ s : S, ∑ a : C, ∑ t : S, ∑ b : C,
      if s = t then F s a b else 0) =
        ∑ s : S, ∑ a : C, ∑ b : C, ∑ t : S,
          if s = t then F s a b else 0 := by
            apply Finset.sum_congr rfl
            intro s _
            apply Finset.sum_congr rfl
            intro a _
            exact Finset.sum_comm
    _ = _ := by simp

/-- Exactly ONE source-defined ordered theta pair with its ORIGINAL
color structure constant. A named term prevents Lean reducing the
underlying Fock SmoothCore when rearranging the finite spin sums. -/
def sourceOriginalFermionColorTerm
    (M : AlgebraData 2) (c : ColorIndex 2)
    (s : SpinIndex) (a b : ColorIndex 2) : SourceEnd 2 :=
  (M.structureConstant a b c : ℂ) •
    (M.fermionAction s a * M.fermionAction s b)

/-- This named term contains the literal original theta actions
in their original order; no surrogate representation is used. -/
theorem sourceOriginalFermionColorTerm_eq_source
    (M : AlgebraData 2) (c : ColorIndex 2)
    (s : SpinIndex) (a b : ColorIndex 2) :
    sourceOriginalFermionColorTerm M c s a b =
      (M.structureConstant a b c : ℂ) •
        (M.fermionAction s a * M.fermionAction s b) := rfl

/-- Original smooth-core fermionic color-current candidate:
(-i/2) ∑_{s,a,b} f_{abc} theta_{s,a} theta_{s,b}.
The named summand is definitionally the exact source expression. -/
def sourceOriginalFermionColorCurrent
    (M : AlgebraData 2) (c : ColorIndex 2) : SourceEnd 2 :=
  (-Complex.I / 2 : ℂ) •
    (∑ s : SpinIndex, ∑ a : ColorIndex 2, ∑ b : ColorIndex 2,
      sourceOriginalFermionColorTerm M c s a b)

/-- The exact spin-Kronecker projection of the SOURCE fermion current.
The original theta order and -i/2 factor are preserved, and the
literal operator identity is inspectable through the term theorem. -/
theorem sourceOriginalFermionColorCurrent_eq_spinDiagonal
    (M : AlgebraData 2) (c : ColorIndex 2) :
    sourceOriginalFermionColorCurrent M c =
      (-Complex.I / 2 : ℂ) •
        (∑ p : FermionLabel 2, ∑ q : FermionLabel 2,
          if p.1 = q.1 then
            sourceOriginalFermionColorTerm M c p.1 p.2 q.2
          else 0) := by
  unfold sourceOriginalFermionColorCurrent
  exact congrArg (fun T : SourceEnd 2 => (-Complex.I / 2 : ℂ) • T)
    (finiteDiagonalSpinProjection
      (fun s a b => sourceOriginalFermionColorTerm M c s a b)).symm

#print axioms finiteDiagonalSpinProjection
#print axioms sourceOriginalFermionColorTerm_eq_source
#print axioms sourceOriginalFermionColorCurrent_eq_spinDiagonal
#check @sourceOriginalFermionColorCurrent_eq_spinDiagonal

end
end FCP.BFSSSU2PhysicalDomainL6G6I
