import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10AEOriginalGammaFourWordTraceZeroProbe

/-!
K1D18V10H-F10AF — all THREE nontrivial shared-index
cross-trace patterns for the ORIGINAL public real gamma pair matrices.

F10AB proved fixed-left shared-index orthogonality, F10AD
qualified simultaneous fixed-left coefficients, and F10AE
proved four-gamma trace zero when the first label differs
from the remaining three. Remaining overlap patterns can
be reduced to the accepted source gamma-square, source
Clifford anticommutation, and cyclic trace identities.

These three exact source-matrix results cover pair words
(a,b)(b,c), (a,b)(c,b), and (a,b)(c,a). They do not assert
any fabricated private gamma table or 48-label replacement.
F10AG can subsequently combine these with accepted F10AB
and F10AE to attempt a FULL distinct-unordered-pair trace
Gram formula and coefficient separation for 36 pair words.

F10AF alone does NOT prove the full 36-family linear
independence, full 256 even-Clifford gamma-image injection,
source Spin9 faithfulness, Spin48 lift, Fock action or
BFSS physical results.

CANDIDATE pending pinned strict Lean warnings-as-errors
compilation and three independent theorem type/axiom audits.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9DetFixture
open OAI.BFSSQuantum
open Matrix

/-- The adjacent shared label b in ORIGINAL gamma words
(a,b)(b,c) cancels by gamma_b²=I. Trace vanishes if
the remaining original labels a and c are distinct. -/
theorem source9OriginalGamma_pair_adjacent_shared_trace_zero
    (a b c : SpaceIndex) (hac : a ≠ c) :
    Matrix.trace ((gamma a * gamma b) * (gamma b * gamma c)) = 0 := by
  have hproduct :
      (gamma a * gamma b) * (gamma b * gamma c) =
        gamma a * gamma c := by
    calc
      (gamma a * gamma b) * (gamma b * gamma c) =
          gamma a * ((gamma b * gamma b) * gamma c) := by
            simp only [mul_assoc]
      _ = gamma a * gamma c := by
            rw [source9OriginalGamma_basis_mul_self b, one_mul]
  rw [hproduct]
  exact source9OriginalGamma_pair_trace_zero a c hac

/-- Two original gamma-pair words sharing their RIGHT
label b have zero cross-trace whenever their LEFT labels
are distinct and c≠b, reducing to -trace(gamma_a gamma_c).
No Fock or Clifford-faithfulness assumptions are used. -/
theorem source9OriginalGamma_pair_shared_right_trace_zero
    (a b c : SpaceIndex) (hac : a ≠ c) (hbc : b ≠ c) :
    Matrix.trace ((gamma a * gamma b) * (gamma c * gamma b)) = 0 := by
  have hproduct :
      (gamma a * gamma b) * (gamma c * gamma b) =
        -(gamma a * gamma c) := by
    calc
      (gamma a * gamma b) * (gamma c * gamma b) =
          gamma a * (gamma b * gamma c) * gamma b := by
            simp only [mul_assoc]
      _ = gamma a * (-(gamma c * gamma b)) * gamma b := by
            rw [source9OriginalGamma_anticommute b c hbc]
      _ = -((gamma a * gamma c) * (gamma b * gamma b)) := by
            simp only [mul_neg, neg_mul, mul_assoc]
      _ = -(gamma a * gamma c) := by
            rw [source9OriginalGamma_basis_mul_self b, mul_one]
  rw [hproduct, Matrix.trace_neg,
    source9OriginalGamma_pair_trace_zero a c hac]
  simp

/-- Cyclic trace moves the closing repeated original
gamma_a in (a,b)(c,a) beside the leading gamma_a;
its square is I, leaving trace(gamma_b gamma_c). -/
theorem source9OriginalGamma_pair_closing_shared_trace_zero
    (a b c : SpaceIndex) (hbc : b ≠ c) :
    Matrix.trace ((gamma a * gamma b) * (gamma c * gamma a)) = 0 := by
  have hcycle :
      Matrix.trace ((gamma a * gamma b) * (gamma c * gamma a)) =
        Matrix.trace (gamma b * gamma c) := by
    calc
      Matrix.trace ((gamma a * gamma b) * (gamma c * gamma a)) =
          Matrix.trace (gamma a * (gamma b * gamma c * gamma a)) := by
            simp only [mul_assoc]
      _ = Matrix.trace ((gamma b * gamma c * gamma a) * gamma a) :=
            Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((gamma b * gamma c) * (gamma a * gamma a)) := by
            simp only [mul_assoc]
      _ = Matrix.trace (gamma b * gamma c) := by
            rw [source9OriginalGamma_basis_mul_self a, mul_one]
  rw [hcycle]
  exact source9OriginalGamma_pair_trace_zero b c hbc

#print axioms source9OriginalGamma_pair_adjacent_shared_trace_zero
#print axioms source9OriginalGamma_pair_shared_right_trace_zero
#print axioms source9OriginalGamma_pair_closing_shared_trace_zero

end
end FCP.BFSSPairedSpin9Clifford
