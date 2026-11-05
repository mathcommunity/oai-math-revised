import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10AAOriginalGammaPairScalarSeparationProbe

/-!
K1D18V10H-F10AB — original 16-real gamma pair
self-norm and shared-index cross-trace separation.

F10AA established trace(γaγb)=0 and γaγb is nonscalar
for a≠b, with the exact PUBLIC original nine gamma fields.
This gate tests a strictly stronger, entry-independent
trace-pairing discriminator:
  (γaγb)^2 = -I16 if a≠b,
  trace((γaγb)^2) = -16 if a≠b,
  trace((γaγb)(γaγc)) = 0 if a≠b and b≠c.

The last identity does not require a≠c. It establishes
vanishing of one family of off-diagonal trace pairings,
not all 36×36 pairings. No 256-word independence, full
source even Clifford gamma injectivity, Spin9 faithfulness,
Spin48 lift, Fock model or BFSS physical result is asserted.

Reuse only accepted original F10E public Clifford relations
and F10AA trace-zero; no private signed-permutation tables,
new source gamma choices, limits or axioms.

CANDIDATE until pinned strict warning-as-error Lean compiler
and three independent declaration type/axiom checks pass.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9DetFixture
open OAI.BFSSQuantum
open Matrix

/-- A genuinely distinct pair of original gamma matrices
squares to negative identity, using ONLY the public source
Clifford relations. -/
theorem source9OriginalGamma_pair_square_neg_one
    (a b : SpaceIndex) (hab : a ≠ b) :
    (gamma a * gamma b) * (gamma a * gamma b) =
      -(1 : GammaMatrix) := by
  calc
    (gamma a * gamma b) * (gamma a * gamma b) =
        gamma a * (gamma b * gamma a) * gamma b := by
          simp only [mul_assoc]
    _ = gamma a * (-(gamma a * gamma b)) * gamma b := by
          rw [source9OriginalGamma_anticommute b a hab.symm]
    _ = -((gamma a * gamma a) * (gamma b * gamma b)) := by
          simp only [mul_neg, neg_mul, mul_assoc]
    _ = -(1 : GammaMatrix) := by
          rw [source9OriginalGamma_basis_mul_self a,
            source9OriginalGamma_basis_mul_self b, one_mul]

/-- Self-pairing by the unnormalized real trace is
the nonzero diagonal coefficient -16. -/
theorem source9OriginalGamma_pair_square_trace_neg_sixteen
    (a b : SpaceIndex) (hab : a ≠ b) :
    Matrix.trace ((gamma a * gamma b) * (gamma a * gamma b)) =
      -(16 : ℝ) := by
  calc
    Matrix.trace ((gamma a * gamma b) * (gamma a * gamma b)) =
        Matrix.trace (-(1 : GammaMatrix)) :=
          congrArg Matrix.trace
            (source9OriginalGamma_pair_square_neg_one a b hab)
    _ = -Matrix.trace (1 : GammaMatrix) := Matrix.trace_neg _
    _ = -(16 : ℝ) := by norm_num [Matrix.trace_one]

/-- Off-diagonal trace-pairing vanishes for original
gamma-pair words with a shared LEFT source index
and distinct RIGHT source labels. The second word need
not have distinct indices internally (a=c is allowed). -/
theorem source9OriginalGamma_pair_shared_left_trace_zero
    (a b c : SpaceIndex) (hab : a ≠ b) (hbc : b ≠ c) :
    Matrix.trace ((gamma a * gamma b) *
      (gamma a * gamma c)) = 0 := by
  have hpair :
      (gamma a * gamma b) * (gamma a * gamma c) =
        -(gamma b * gamma c) := by
    calc
      (gamma a * gamma b) * (gamma a * gamma c) =
          gamma a * (gamma b * gamma a) * gamma c := by
            simp only [mul_assoc]
      _ = gamma a * (-(gamma a * gamma b)) * gamma c := by
            rw [source9OriginalGamma_anticommute b a hab.symm]
      _ = -((gamma a * gamma a) * (gamma b * gamma c)) := by
            simp only [mul_neg, neg_mul, mul_assoc]
      _ = -(gamma b * gamma c) := by
            rw [source9OriginalGamma_basis_mul_self a, one_mul]
  rw [hpair, Matrix.trace_neg,
    source9OriginalGamma_pair_trace_zero b c hbc]
  simp

#print axioms source9OriginalGamma_pair_square_neg_one
#print axioms source9OriginalGamma_pair_square_trace_neg_sixteen
#print axioms source9OriginalGamma_pair_shared_left_trace_zero

end
end FCP.BFSSPairedSpin9Clifford
