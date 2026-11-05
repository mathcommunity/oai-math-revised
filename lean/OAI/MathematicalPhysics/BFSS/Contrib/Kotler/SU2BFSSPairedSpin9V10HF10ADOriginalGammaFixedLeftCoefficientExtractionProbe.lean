import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10ACOriginalGammaFixedLeftPairDiscriminationProbe

/-!
K1D18V10H-F10AD — exact source gamma fixed-left FINITE
coefficient extraction, beyond pairwise nonproportionality.

The accepted original F10AC trace Gram formula isolates
each real coefficient f(b) (b≠a) in a FINITE LINEAR
COMBINATION of the original matrices gamma a * gamma c.

Prove:
* Trace pairing with gamma a * gamma b equals -16*f b.
* If the full nine-term matrix combination is zero,
  then all nontrivial b≠a coefficients must vanish.
* If the scalar coefficient f a also vanishes, the
  entire coefficient function is zero.

This establishes SIMULTANEOUS real-linear separation
of the eight genuine fixed-left nontrivial gamma-pair
words, NOT merely two-word nonproportionality. It does
NOT show all 36 gamma-pair images independent, all 256
even PBW gamma images independent, full even-Clifford
gamma AlgHom injectivity, source Spin9 faithfulness,
Spin48 lift, Fock or BFSS spectral physics.

Use only actual source gamma family and accepted F10AC
trace pairing; no private gamma tables, new matrix
representation, resource-limit changes or axioms.

CANDIDATE pending exact pinned strict warning-as-error
Lean compilation and independent source type/axiom gates.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open OAI.BFSSQuantum
open Matrix

/-- The original gamma-pair trace Gram functional extracts
the EXACT coefficient -(16)*f(b) from any nine-label real
linear combination, whenever b differs from fixed left a.
No f(a)=0 hypothesis is needed: the scalar gamma_a^2=1
term is trace-orthogonal to gamma_a gamma_b. -/
theorem source9OriginalGamma_fixed_left_trace_extract
    (a b : SpaceIndex) (hab : a ≠ b)
    (f : SpaceIndex → ℝ) :
    Matrix.trace ((gamma a * gamma b) *
      (∑ c : SpaceIndex, f c • (gamma a * gamma c))) =
      -(16 : ℝ) * f b := by
  calc
    Matrix.trace ((gamma a * gamma b) *
        (∑ c : SpaceIndex, f c • (gamma a * gamma c))) =
        ∑ c : SpaceIndex, Matrix.trace
          ((gamma a * gamma b) *
            (f c • (gamma a * gamma c))) := by
      rw [Matrix.mul_sum, Matrix.trace_sum]
    _ = ∑ c : SpaceIndex,
        f c * (if b = c then -(16 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [mul_smul_comm, Matrix.trace_smul,
        source9OriginalGamma_fixed_left_pair_trace_gram a b c hab]
      simp only [smul_eq_mul]
    _ = -(16 : ℝ) * f b := by
      classical
      simp only [mul_ite, mul_zero]
      simp [mul_comm]

/-- Zero original gamma fixed-left family combination
forces EVERY genuinely nontrivial index coefficient
f(b) to vanish (a≠b). This is simultaneous coefficient
separation, not just inequality of two matrix words. -/
theorem source9OriginalGamma_fixed_left_coeff_zero
    (a : SpaceIndex) (f : SpaceIndex → ℝ)
    (hsum :
      (∑ c : SpaceIndex, f c • (gamma a * gamma c)) =
        (0 : GammaMatrix))
    (b : SpaceIndex) (hab : a ≠ b) :
    f b = 0 := by
  have ht := congrArg
    (fun M : GammaMatrix =>
      Matrix.trace ((gamma a * gamma b) * M)) hsum
  rw [source9OriginalGamma_fixed_left_trace_extract a b hab f] at ht
  have hzero : -(16 : ℝ) * f b = 0 := by
    simpa using ht
  have h16 : (-(16 : ℝ)) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hzero).resolve_left h16

/-- Source-exact fixed-left finite combination injectivity
ON THE NONTRIVIAL EIGHT-WORD SUBFAMILY, expressed as
f(a)=0. The scalar index a is not claimed to be separated
by these pair-only trace functionals. -/
theorem source9OriginalGamma_fixed_left_coeff_function_zero
    (a : SpaceIndex) (f : SpaceIndex → ℝ)
    (ha : f a = 0)
    (hsum :
      (∑ c : SpaceIndex, f c • (gamma a * gamma c)) =
        (0 : GammaMatrix)) :
    f = 0 := by
  funext b
  by_cases hab : a = b
  · subst b
    exact ha
  · exact source9OriginalGamma_fixed_left_coeff_zero a f hsum b hab

#print axioms source9OriginalGamma_fixed_left_trace_extract
#print axioms source9OriginalGamma_fixed_left_coeff_zero
#print axioms source9OriginalGamma_fixed_left_coeff_function_zero

end
end FCP.BFSSPairedSpin9Clifford
