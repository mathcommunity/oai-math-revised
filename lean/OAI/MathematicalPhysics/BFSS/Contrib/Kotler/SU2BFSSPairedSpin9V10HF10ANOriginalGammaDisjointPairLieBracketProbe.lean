import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10AMOriginalGammaOrderedSharedRightLieBracketProbe

/-!
K1D18V10H-F10AN — ORIGINAL source gamma disjoint-pair
Lie bracket, the four-distinct-index case.

Accepted F10AK/F10AL/F10AM establish the three nontrivial
three-index overlap patterns for canonical gamma pairs
in Mathlib's actual native orthogonal so(16,R) Lie algebra.

The independent four-index pattern must not be inferred
from orthogonality of matrix traces. Instead this module
proves a general pair/single COMMUTATION identity using
TWO accepted public Clifford anticommutations, then
commutation of disjoint pairs by applying it TWICE.
This gives a zero source matrix commutator and a zero
native so(16,R) Lie bracket, with all cross-index
inequalities explicitly supplied.

The exact real 16x16 original source gamma matrices,
SpaceIndex = Fin 9, canonical pair subtype and
Mathlib native so(16,R) carrier are retained. No
private signed-permutation data or surrogate matrices.

This does NOT establish a complete bracket formula for
all 36 pair indices: overlapping patterns in arbitrary
relative ordering and same-pair cases still require
a source-exact assembly. No so(9) -> so(16) LieHom,
Clifford even 256-image independence or injection,
global Spin(9)/Spin(48) lift, source Fock action or
BFSS physical/spectral result is claimed.

CANDIDATE until pinned Lean warnings-as-errors compile
and FOUR independent declaration-type/root-axiom audits.
No sorry, axioms, native_decide, raised resource limits,
or changes to any previously qualified source.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9DetFixture
open OAI.BFSSQuantum
open Matrix

/-- An ORIGINAL gamma pair commutes with a third original
gamma matrix when both of its labels are distinct from
that third label: moving the third gamma past TWO
anticommuting factors cancels both minus signs. -/
theorem source9OriginalGamma_disjoint_pair_single_commute
    (a b c : SpaceIndex) (hac : a ≠ c) (hbc : b ≠ c) :
    (gamma a * gamma b) * gamma c =
      gamma c * (gamma a * gamma b) := by
  calc
    (gamma a * gamma b) * gamma c =
        gamma a * (gamma b * gamma c) := by
          rw [mul_assoc]
    _ = gamma a * (-(gamma c * gamma b)) := by
          rw [source9OriginalGamma_anticommute b c hbc]
    _ = -(gamma a * (gamma c * gamma b)) := by
          rw [mul_neg]
    _ = -((gamma a * gamma c) * gamma b) := by
          rw [← mul_assoc]
    _ = -((-(gamma c * gamma a)) * gamma b) := by
          rw [source9OriginalGamma_anticommute a c hac]
    _ = (gamma c * gamma a) * gamma b := by
          simp only [neg_mul, neg_neg]
    _ = gamma c * (gamma a * gamma b) := by
          rw [mul_assoc]

/-- Every two disjoint ORIGINAL gamma-pair matrices
commute, regardless of the order of the four distinct
labels. This is a source-equality, not a trace identity. -/
theorem source9OriginalGamma_disjoint_pair_commute
    (a b c d : SpaceIndex)
    (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    (gamma c * gamma d) * (gamma a * gamma b) =
      (gamma a * gamma b) * (gamma c * gamma d) := by
  calc
    (gamma c * gamma d) * (gamma a * gamma b) =
        ((gamma c * gamma d) * gamma a) * gamma b := by
          rw [← mul_assoc]
    _ = (gamma a * (gamma c * gamma d)) * gamma b := by
          rw [source9OriginalGamma_disjoint_pair_single_commute
            c d a hac.symm had.symm]
    _ = gamma a * ((gamma c * gamma d) * gamma b) := by
          rw [mul_assoc]
    _ = gamma a * (gamma b * (gamma c * gamma d)) := by
          rw [source9OriginalGamma_disjoint_pair_single_commute
            c d b hbc.symm hbd.symm]
    _ = (gamma a * gamma b) * (gamma c * gamma d) := by
          rw [← mul_assoc]

/-- The exact original real matrix commutator of disjoint
gamma-pair words vanishes. -/
theorem source9OriginalGamma_disjoint_pair_matrix_commutator_zero
    (a b c d : SpaceIndex)
    (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    (gamma a * gamma b) * (gamma c * gamma d) -
      (gamma c * gamma d) * (gamma a * gamma b) =
        (0 : GammaMatrix) := by
  rw [source9OriginalGamma_disjoint_pair_commute
    a b c d hac had hbc hbd]
  exact sub_self _

/-- In Mathlib's NATIVE orthogonal so(16,R), the two
original canonically indexed gamma-pair elements have
zero Lie bracket when their source labels are disjoint.
This includes ALL four-distinct relative index orders. -/
theorem source9OriginalGamma_disjoint_pair_native_so_bracket_zero
    (a b c d : SpaceIndex)
    (hab : a < b) (hcd : c < d)
    (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    ⁅source9OrderedGammaPairInSo ⟨(a,b),hab⟩,
      source9OrderedGammaPairInSo ⟨(c,d),hcd⟩⁆ =
        (0 : LieAlgebra.Orthogonal.so SpinIndex ℝ) := by
  apply Subtype.ext
  change (gamma a * gamma b) * (gamma c * gamma d) -
    (gamma c * gamma d) * (gamma a * gamma b) =
      (0 : GammaMatrix)
  exact source9OriginalGamma_disjoint_pair_matrix_commutator_zero
    a b c d hac had hbc hbd

#print axioms source9OriginalGamma_disjoint_pair_single_commute
#print axioms source9OriginalGamma_disjoint_pair_commute
#print axioms source9OriginalGamma_disjoint_pair_matrix_commutator_zero
#print axioms source9OriginalGamma_disjoint_pair_native_so_bracket_zero

end
end FCP.BFSSPairedSpin9Clifford
