import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF8CliffordUnitsGeneratorDetBridgeProbe
import Mathlib.Algebra.Ring.Commute

/-!
K1D18V10H-F9 — exact determinant magnitude of the genuine
nine-source Clifford vector gamma generator.

Use ONLY the original accepted gammaNineRealLinear_sq
Clifford all-vector square identity, matrix determinant
multiplicativity and Matrix.det_smul in exactly the
original Fin 16 gamma representation.

Results targeted:
det(Gamma(v))^2 = Q(v)^16;
det(Gamma(v)) = +Q(v)^8 OR -Q(v)^8.
Transfer this genuine sign/magnitude alternative to an
actual original Clifford vector UNIT, using accepted F8.

This narrows the concrete generator problem but DOES NOT
choose the sign, prove a positive determinant on all
generators, prove the source Spin9 orientation character
trivial, or assume square generation / perfectness.
No continuity, Spin48 lifting or BFSS physical claim.

F9 CANDIDATE until full source-exact strict CI.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- Exact determinant-square identity for each original
nine-source real gamma linear combination, with the actual
16-real-dimensional index. -/
theorem gammaNineRealLinear_det_sq16
    (v : SpaceIndex → ℝ) :
    (gammaNineRealLinear v).det ^ 2 =
      (source9Quadratic v) ^ 16 := by
  have h := congrArg Matrix.det (gammaNineRealLinear_sq v)
  simpa only [Matrix.det_mul, Matrix.det_smul,
    Matrix.det_one, mul_one, Fintype.card_fin, pow_two] using h

/-- Pure algebra gives the two exact determinant branches
for the ORIGINAL real gamma16 generator. Neither branch
is selected here, including for positive Q(v). -/
theorem gammaNineRealLinear_det_eq_pow8_or_neg
    (v : SpaceIndex → ℝ) :
    (gammaNineRealLinear v).det = (source9Quadratic v) ^ 8 ∨
      (gammaNineRealLinear v).det = -(source9Quadratic v) ^ 8 := by
  have hsq :
      (gammaNineRealLinear v).det * (gammaNineRealLinear v).det =
        (source9Quadratic v)^8 * (source9Quadratic v)^8 := by
    calc
      (gammaNineRealLinear v).det * (gammaNineRealLinear v).det =
          (source9Quadratic v) ^ 16 := by
        simpa only [pow_two] using gammaNineRealLinear_det_sq16 v
      _ = (source9Quadratic v)^8 * (source9Quadratic v)^8 := by
        simpa only [show 8 + 8 = 16 by decide] using
          (pow_add (source9Quadratic v) 8 8)
  exact (mul_self_eq_mul_self_iff).mp hsq

/-- The accepted ambient original Clifford units determinant
has this same two-branch formula whenever the ACTUAL
underlying Clifford element is an original vector
generator. This is not a positive-sign assertion. -/
theorem source9CliffordUnitsGammaDetHom_generator_two_sign
    (u : (CliffordAlgebra source9Quadratic)ˣ)
    (v : SpaceIndex → ℝ)
    (hvec : (u : CliffordAlgebra source9Quadratic) =
      CliffordAlgebra.ι source9Quadratic v) :
    source9CliffordUnitsGammaDetHom u = (source9Quadratic v) ^ 8 ∨
      source9CliffordUnitsGammaDetHom u = -(source9Quadratic v) ^ 8 := by
  rw [source9CliffordUnitsGammaDetHom_generator u v hvec]
  exact gammaNineRealLinear_det_eq_pow8_or_neg v

#print axioms gammaNineRealLinear_det_sq16
#print axioms gammaNineRealLinear_det_eq_pow8_or_neg
#print axioms source9CliffordUnitsGammaDetHom_generator_two_sign

end
end FCP.BFSSPairedSpin9DetFixture
