import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10ADOriginalGammaFixedLeftCoefficientExtractionProbe

/-!
K1D18V10H-F10AE — ORIGINAL source real gamma length-four
trace orthogonality, using accepted public Clifford relations.

F10AD qualified simultaneous coefficient extraction for all
eight nontrivial gamma pair words with a fixed left index.
To advance toward the full 36-pair trace Gram matrix, this
gate proves trace zero for a four-gamma word when its first
source index differs from each of its three other indices.

Proof: three source anticommutations move gamma_a across
gamma_b gamma_c gamma_d, yielding a negative; trace cyclicity
makes the same trace its own negative. No gamma table access,
replacement matrices, surrogate Clifford carrier or index
flattening is used.

Then identify the result with trace((gamma_a gamma_b)
(gamma_c gamma_d)); in particular the result applies
to genuinely disjoint original source gamma pairs.
This does NOT establish the complete unordered-pair Gram
formula, independence of 36 pair words, independence of
256 even Clifford words, original Spin9 faithfulness,
Spin48 lift, Fock implementation or BFSS physics.

CANDIDATE pending pinned strict warning-as-error compiler
and two independent source exact declaration/axiom checks.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9DetFixture
open OAI.BFSSQuantum
open Matrix

/-- Original gamma product trace vanishes if its first
source index differs from the other three source indices.
The other three may repeat; the proof does not assume
an unverified independence of all four gamma matrices. -/
theorem source9OriginalGamma_four_word_trace_zero
    (a b c d : SpaceIndex)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    Matrix.trace
      (gamma a * (gamma b * gamma c * gamma d)) = 0 := by
  have hmove :
      (gamma b * gamma c * gamma d) * gamma a =
        -(gamma a * (gamma b * gamma c * gamma d)) := by
    calc
      (gamma b * gamma c * gamma d) * gamma a =
          gamma b * (gamma c * (gamma d * gamma a)) := by
            simp only [mul_assoc]
      _ = gamma b * (gamma c * (-(gamma a * gamma d))) := by
            rw [source9OriginalGamma_anticommute d a had.symm]
      _ = -(gamma b * (gamma c * (gamma a * gamma d))) := by
            simp only [mul_neg]
      _ = -(gamma b * ((gamma c * gamma a) * gamma d)) := by
            simp only [mul_assoc]
      _ = -(gamma b * ((-(gamma a * gamma c)) * gamma d)) := by
            rw [source9OriginalGamma_anticommute c a hac.symm]
      _ = gamma b * (gamma a * (gamma c * gamma d)) := by
            simp only [neg_mul, mul_neg, mul_assoc, neg_neg]
      _ = (gamma b * gamma a) * (gamma c * gamma d) := by
            exact (mul_assoc _ _ _).symm
      _ = (-(gamma a * gamma b)) * (gamma c * gamma d) := by
            rw [source9OriginalGamma_anticommute b a hab.symm]
      _ = -(gamma a * (gamma b * gamma c * gamma d)) := by
            simp only [neg_mul, mul_assoc]
  have hcyclic :
      Matrix.trace (gamma a *
          (gamma b * gamma c * gamma d)) =
        Matrix.trace ((gamma b * gamma c * gamma d) * gamma a) :=
    Matrix.trace_mul_comm _ _
  have hneg :
      Matrix.trace (gamma a *
          (gamma b * gamma c * gamma d)) =
        -Matrix.trace (gamma a *
          (gamma b * gamma c * gamma d)) := by
    calc
      Matrix.trace (gamma a * (gamma b * gamma c * gamma d)) =
          Matrix.trace ((gamma b * gamma c * gamma d) * gamma a) :=
            hcyclic
      _ = -Matrix.trace
          (gamma a * (gamma b * gamma c * gamma d)) := by
            rw [hmove, Matrix.trace_neg]
  linarith

/-- Original source gamma pair trace pairing vanishes
when the left index of the first pair differs from
all three of the other indicated indices. This covers
in particular all four-distinct pair-index cases. -/
theorem source9OriginalGamma_pair_four_word_trace_zero
    (a b c d : SpaceIndex)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    Matrix.trace ((gamma a * gamma b) * (gamma c * gamma d)) = 0 := by
  simpa only [mul_assoc] using
    (source9OriginalGamma_four_word_trace_zero a b c d hab hac had)

#print axioms source9OriginalGamma_four_word_trace_zero
#print axioms source9OriginalGamma_pair_four_word_trace_zero

end
end FCP.BFSSPairedSpin9Clifford
