import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10AHOriginalGammaAllOrderedPairCoefficientExtractionProbe

/-!
K1D18V10H-F10AI — Mathlib LinearIndependent bridge for
ALL 36 canonical original gamma-pair matrices.

F10AH accepted the strongest necessary source-exact
coefficient uniqueness result: if an arbitrary real linear
combination of all canonical source gamma pair matrices
is zero, its coefficient function is identically zero.

This gate bridges that EXACT theorem, without re-proving
or approximating it, to Mathlib's official
LinearIndependent predicate using the pinned-source lemma
Fintype.linearIndependent_iff, then obtains uniqueness
of two arbitrary coefficient representations using the
pinned-source Fintype.linearIndependent_iffₛ.

Source indices are the ORIGINAL SpaceIndex = Fin 9.
The domain Source9OrderedGammaPairIndex consists of
a<b canonical pairs of those source indices (36 members).
The target is the ORIGINAL GammaMatrix = 16×16 real
source gamma representation.

The bridge does NOT infer the 256 even original Clifford
PBW image family, its linear independence/injectivity,
source Spin9 faithfulness, global Spin48 lift, Fock
operators or BFSS physical or spectral conclusions.
No private matrix tables, surrogate gamma maps,
new axioms, sorry, or resource-limit changes.

CANDIDATE until exact pinned warning-as-error Lean
compilation and two independent theorem type/axiom audits.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open OAI.BFSSQuantum
open Matrix

/-- EXACT Mathlib LinearIndependent predicate for the
full 36-element family of original source gamma pair
matrices, derived solely from accepted F10AH coefficient
uniqueness. -/
theorem source9OriginalGamma_all_ordered_pairs_linearIndependent :
    LinearIndependent ℝ source9OrderedGammaPairMatrix := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro f hsum p
  have hf :
      f = 0 :=
    source9OriginalGamma_all_ordered_pairs_coeff_function_zero f hsum
  simpa using congrFun hf p

/-- Any two real coefficient representations by ALL 36
original canonically oriented gamma pair matrices agree
termwise when their source matrices are equal. -/
theorem source9OriginalGamma_all_ordered_pairs_coeff_unique
    (f g : Source9OrderedGammaPairIndex → ℝ)
    (hfg :
      (∑ p : Source9OrderedGammaPairIndex,
        f p • source9OrderedGammaPairMatrix p) =
      (∑ p : Source9OrderedGammaPairIndex,
        g p • source9OrderedGammaPairMatrix p)) :
    f = g := by
  classical
  funext p
  exact (Fintype.linearIndependent_iffₛ.mp
    source9OriginalGamma_all_ordered_pairs_linearIndependent
    f g hfg) p

#print axioms source9OriginalGamma_all_ordered_pairs_linearIndependent
#print axioms source9OriginalGamma_all_ordered_pairs_coeff_unique

end
end FCP.BFSSPairedSpin9Clifford
