import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10AGOriginalGammaOrderedPairGramProbe

/-!
K1D18V10H-F10AH — source-exact FULL 36 gamma pair coefficient separation.

F10AG qualified the signed trace Gram delta for EVERY
canonically ordered original source pair a<b and c<d.
This file defines the actual subtype of canonical pairs,
maps each pair to gamma_a gamma_b in the ORIGINAL
16-by-16 real source gamma matrices, and extracts every
coefficient from an arbitrary finite linear combination.

There are 36 such original source pairs because
SpaceIndex = Fin 9. The theorem's exact statement
covers the entire canonical subtype, not a hand-selected
subset or a surrogate representation.

Qualification goal:
* source9OriginalGamma_ordered_pair_subtype_trace_gram
* source9OriginalGamma_all_ordered_pairs_trace_extract
* source9OriginalGamma_all_ordered_pairs_coeff_function_zero

The third theorem is a simultaneous 36-word coefficient
uniqueness certificate: if the original pair matrix sum
is zero, the coefficient function must be zero. It does
not yet assert the formal Mathlib LinearIndependent
predicate (a separate bridge), the 256 even Clifford PBW
gamma-image independence, full even Clifford gamma AlgHom
injectivity, faithful source Spin9 action, global Spin48
lift, Fock action or BFSS physical spectral existence.

No private signed-permutation gamma data, replacement
matrices, unstated PBW multiplicativity, new axioms,
sorry, or increased resource limits.

CANDIDATE until strict Lean warnings-as-errors and all
three independently elaborated exact theorem type/axiom
audits pass.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open OAI.BFSSQuantum
open Matrix

/-- Canonically oriented pairs of ORIGINAL nine source
space indices. Equivalently the 36 unordered pairs. -/
abbrev Source9OrderedGammaPairIndex :=
  {p : SpaceIndex × SpaceIndex // p.1 < p.2}

/-- Actual gamma-pair product in the source 16-real
gamma representation. It is not a replacement matrix. -/
abbrev source9OrderedGammaPairMatrix
    (p : Source9OrderedGammaPairIndex) : GammaMatrix :=
  gamma p.val.1 * gamma p.val.2

/-- Exact -16 times the Kronecker delta on the ORIGINAL
canonical pair subtype, imported from the source-exact
F10AG Gram theorem. -/
theorem source9OriginalGamma_ordered_pair_subtype_trace_gram
    (p q : Source9OrderedGammaPairIndex) :
    Matrix.trace (source9OrderedGammaPairMatrix p *
      source9OrderedGammaPairMatrix q) =
      if p = q then -(16 : ℝ) else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    simpa [source9OrderedGammaPairMatrix] using
      (source9OriginalGamma_pair_square_trace_neg_sixteen
        p.val.1 p.val.2 (ne_of_lt p.property))
  · have hneq :
        (p.val.1, p.val.2) ≠ (q.val.1, q.val.2) := by
      intro hpv
      exact hpq (Subtype.ext (by simpa using hpv))
    have htrace :=
      source9OriginalGamma_ordered_distinct_pair_trace_zero
        p.val.1 p.val.2 q.val.1 q.val.2
        p.property q.property hneq
    simpa [source9OrderedGammaPairMatrix, hpq] using htrace

/-- Extract ANY one coefficient of an arbitrary finite
real linear combination of ALL 36 original gamma-pair
matrices using the signed source trace Gram functional. -/
theorem source9OriginalGamma_all_ordered_pairs_trace_extract
    (p : Source9OrderedGammaPairIndex)
    (f : Source9OrderedGammaPairIndex → ℝ) :
    Matrix.trace (source9OrderedGammaPairMatrix p *
      (∑ q : Source9OrderedGammaPairIndex,
        f q • source9OrderedGammaPairMatrix q)) =
      -(16 : ℝ) * f p := by
  classical
  calc
    Matrix.trace (source9OrderedGammaPairMatrix p *
        (∑ q : Source9OrderedGammaPairIndex,
          f q • source9OrderedGammaPairMatrix q)) =
        ∑ q : Source9OrderedGammaPairIndex,
          Matrix.trace (source9OrderedGammaPairMatrix p *
            (f q • source9OrderedGammaPairMatrix q)) := by
      rw [Matrix.mul_sum, Matrix.trace_sum]
    _ = ∑ q : Source9OrderedGammaPairIndex,
        f q * (if p = q then -(16 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [mul_smul_comm, Matrix.trace_smul,
        source9OriginalGamma_ordered_pair_subtype_trace_gram p q]
      simp only [smul_eq_mul]
    _ = -(16 : ℝ) * f p := by
      simp only [mul_ite, mul_zero]
      simp [mul_comm]

/-- SIMULTANEOUS source-exact independence certificate:
the ONLY real coefficient function on all 36 canonical
source gamma pairs whose original 16-real gamma-matrix
linear combination is zero is the zero function. -/
theorem source9OriginalGamma_all_ordered_pairs_coeff_function_zero
    (f : Source9OrderedGammaPairIndex → ℝ)
    (hsum :
      (∑ q : Source9OrderedGammaPairIndex,
        f q • source9OrderedGammaPairMatrix q) =
          (0 : GammaMatrix)) :
    f = 0 := by
  funext p
  have ht := congrArg
    (fun M : GammaMatrix =>
      Matrix.trace (source9OrderedGammaPairMatrix p * M)) hsum
  rw [source9OriginalGamma_all_ordered_pairs_trace_extract p f] at ht
  have hzero : -(16 : ℝ) * f p = 0 := by
    simpa using ht
  exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)

#print axioms source9OriginalGamma_ordered_pair_subtype_trace_gram
#print axioms source9OriginalGamma_all_ordered_pairs_trace_extract
#print axioms source9OriginalGamma_all_ordered_pairs_coeff_function_zero

end
end FCP.BFSSPairedSpin9Clifford
