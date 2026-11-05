import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10ABOriginalGammaPairTraceOrthogonalityProbe

/-!
K1D18V10H-F10AC — exact original gamma fixed-left Gram
identity and two-word NONPROPORTIONALITY.

The accepted F10AB original gamma trace pairings yield a
source-exact Kronecker-delta Gram formula for original
sixteen-real gamma words sharing their first source label.
Its nonzero diagonal and zero off-diagonal entries imply
a pair of distinct right-label words cannot be real scalar
multiples, a genuine two-word linear-separation theorem.

This does NOT prove linear independence of all eight
fixed-left words simultaneously, all 36 gamma pairs, or
all 256 original even Clifford gamma-image basis elements.
No full source Spin9 faithfulness, Spin48 lift, Fock action
or BFSS spectral physical result is claimed.

Use ONLY accepted F10AB original gamma sources and F10E
public Clifford law, not private permutation tables or
surrogate matrices. CANDIDATE until strict compiler and
three independent exact type/axiom audits.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open OAI.BFSSQuantum
open Matrix

/-- Exact signed Gram matrix for original gamma-pair words
with common first index a and nontrivial first word a≠b. -/
theorem source9OriginalGamma_fixed_left_pair_trace_gram
    (a b c : SpaceIndex) (hab : a ≠ b) :
    Matrix.trace ((gamma a * gamma b) * (gamma a * gamma c)) =
      if b = c then -(16 : ℝ) else 0 := by
  by_cases hbc : b = c
  · subst c
    simpa using
      (source9OriginalGamma_pair_square_trace_neg_sixteen a b hab)
  · simpa [hbc] using
      (source9OriginalGamma_pair_shared_left_trace_zero a b c hab hbc)

/-- Two original gamma words with common first label
and DISTINCT second labels have unequal matrix images. -/
theorem source9OriginalGamma_fixed_left_pair_ne
    (a b c : SpaceIndex) (hab : a ≠ b) (hbc : b ≠ c) :
    gamma a * gamma b ≠ gamma a * gamma c := by
  intro heq
  have htrace := congrArg
    (fun M : GammaMatrix =>
      Matrix.trace ((gamma a * gamma b) * M)) heq
  rw [source9OriginalGamma_pair_square_trace_neg_sixteen a b hab,
    source9OriginalGamma_pair_shared_left_trace_zero a b c hab hbc] at htrace
  norm_num at htrace

/-- Two different original gamma words sharing the first
source index are NOT real scalar multiples. Unlike mere
pair inequivalence, this supplies a genuine two-word
linear-separation certificate. The second word may be
scalar (if a=c), but the first word is not. -/
theorem source9OriginalGamma_fixed_left_pair_not_smul
    (a b c : SpaceIndex) (hab : a ≠ b) (hbc : b ≠ c) (r : ℝ) :
    gamma a * gamma b ≠ r • (gamma a * gamma c) := by
  intro heq
  have hright :
      Matrix.trace ((gamma a * gamma b) *
        (r • (gamma a * gamma c))) = 0 := by
    rw [mul_smul_comm, Matrix.trace_smul,
      source9OriginalGamma_pair_shared_left_trace_zero a b c hab hbc]
    simp
  have hcontra :
      -(16 : ℝ) = 0 := by
    calc
      -(16 : ℝ) =
          Matrix.trace ((gamma a * gamma b) * (gamma a * gamma b)) :=
        (source9OriginalGamma_pair_square_trace_neg_sixteen a b hab).symm
      _ = Matrix.trace ((gamma a * gamma b) *
          (r • (gamma a * gamma c))) := congrArg
            (fun M : GammaMatrix =>
              Matrix.trace ((gamma a * gamma b) * M)) heq
      _ = 0 := hright
  norm_num at hcontra

#print axioms source9OriginalGamma_fixed_left_pair_trace_gram
#print axioms source9OriginalGamma_fixed_left_pair_ne
#print axioms source9OriginalGamma_fixed_left_pair_not_smul

end
end FCP.BFSSPairedSpin9Clifford
