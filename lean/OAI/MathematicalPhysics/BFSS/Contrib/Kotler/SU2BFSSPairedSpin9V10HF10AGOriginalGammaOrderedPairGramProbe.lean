import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10AFOriginalGammaSharedIndexCrossTraceProbe

/-!
K1D18V10H-F10AG — FULL source EXACT 36 unordered-pair
trace Gram matrix for the ORIGINAL nine sixteen-real gamma
matrices, indexed canonically by a<b and c<d.

Accepted F10AB: gamma-pair diagonal trace -16 and
common-left cross-trace zero.
Accepted F10AE: four-word trace zero with first
index distinct from the other three.
Accepted F10AF: adjacent-shared, right-shared and
closing-shared index cross-traces zero.

The canonical source order a<b forbids reversed-pair
duplicates, which would otherwise have trace +16.
The present two candidate lemmas use exhaustive equality
case distinctions to prove off-diagonal trace zero and
the FULL signed Gram delta for all canonically ordered
two-letter gamma words.

This is NOT yet formal linear independence of 36 finite
words; no 36-word coefficient function has been defined or
separated in this module. Does NOT establish 256 even
Clifford gamma-image independence/injectivity, faithful
source Spin9 action, Spin48 global lift, Fock action or
physical BFSS spectral claims.

Only actual source public gamma Clifford relations and
accepted F10AF ancestry are used. No private matrices,
surrogate representations or index-order shortcuts.
CANDIDATE pending strict compiler and independent
exact declaration type/axiom audits.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open OAI.BFSSQuantum
open Matrix

/-- For distinct canonically ordered source gamma pairs
a<b and c<d, their ORIGINAL sixteen-real matrix products
are orthogonal under unnormalized trace(M*N). All overlap
patterns are dispatched to the independently accepted
F10AB/F10AE/F10AF source lemmas. -/
theorem source9OriginalGamma_ordered_distinct_pair_trace_zero
    (a b c d : SpaceIndex)
    (hab : a < b) (hcd : c < d)
    (hpair : (a,b) ≠ (c,d)) :
    Matrix.trace ((gamma a * gamma b) *
      (gamma c * gamma d)) = 0 := by
  by_cases hac : a = c
  · subst c
    have hbd : b ≠ d := by
      intro hbd
      subst d
      exact hpair rfl
    exact source9OriginalGamma_pair_shared_left_trace_zero
      a b d (ne_of_lt hab) hbd
  · by_cases had : a = d
    · subst d
      have hbc : b ≠ c := ne_of_gt (hcd.trans hab)
      exact source9OriginalGamma_pair_closing_shared_trace_zero
        a b c hbc
    · by_cases hbc : b = c
      · subst c
        have had' : a ≠ d := ne_of_lt (hab.trans hcd)
        exact source9OriginalGamma_pair_adjacent_shared_trace_zero
          a b d had'
      · by_cases hbd : b = d
        · subst d
          have hbc' : b ≠ c := ne_of_gt hcd
          exact source9OriginalGamma_pair_shared_right_trace_zero
            a b c hac hbc'
        · exact source9OriginalGamma_pair_four_word_trace_zero
            a b c d (ne_of_lt hab) hac had

/-- Complete signed trace Gram formula for the 36
canonically ordered, original source gamma-pair words:
-16 for the SAME a<b pair and zero for DISTINCT pairs.
No formal 36-word coefficient extraction is claimed. -/
theorem source9OriginalGamma_ordered_pair_trace_gram
    (a b c d : SpaceIndex)
    (hab : a < b) (hcd : c < d) :
    Matrix.trace ((gamma a * gamma b) *
      (gamma c * gamma d)) =
      if (a,b) = (c,d) then -(16 : ℝ) else 0 := by
  by_cases hpair : (a,b) = (c,d)
  · rcases Prod.mk.inj hpair with ⟨hac, hbd⟩
    subst c
    subst d
    simpa using
      (source9OriginalGamma_pair_square_trace_neg_sixteen
        a b (ne_of_lt hab))
  · simpa [hpair] using
      (source9OriginalGamma_ordered_distinct_pair_trace_zero
        a b c d hab hcd hpair)

#print axioms source9OriginalGamma_ordered_distinct_pair_trace_zero
#print axioms source9OriginalGamma_ordered_pair_trace_gram

end
end FCP.BFSSPairedSpin9Clifford
