import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF9GeneratorDeterminantMagnitudeProbe
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
K1D18V10H-F10E — publicly typed original nine-gamma
anticommutation and trace-zero bridge.

V10H-F10 original gamma8 direct matrix diagonal proof failed
three times because the signed-permutation gammaInt, perm,
sign tables are PRIVATE inside the original frozen legacy
SU2RealGammaProbe.lean. F10D 'import all' was rejected by the
pinned parser because this is NOT a module-system source.

Do not mutate the accepted original source, copy private
signed-permutation tables, raise limits, or add proof axioms.

Instead prove a genuinely useful matrix invariant using ONLY
the accepted PUBLIC original gamma_clifford theorem:
  gamma_i ^ 2 = I;
  gamma_i gamma_j = -(gamma_j gamma_i), for i≠j;
  trace gamma_i = 0, using inverse conjugation and trace
    cyclicity (the other gamma_j is its own inverse);
  trace (sum v_i gamma_i) = 0, for EVERY source real
    nine-vector and the exact original SpinIndex Fin16.

Trace zero plus the qualified F9 determinant magnitude is a
strict, source-exact input for a future eigenmultiplicity
or characteristic-polynomial argument to choose sign.
No determinant sign is inferred here. No substitute gamma,
Spin group, Clifford representation or Fock ordering.

F10E is UNQUALIFIED until pinned strict compiler and four
independent exact-type/axiom checks pass.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- Original PUBLIC Clifford law implies each exact original
signed-permutation gamma basis matrix squares to I. -/
theorem source9OriginalGamma_basis_mul_self (a : SpaceIndex) :
    gamma a * gamma a = (1 : GammaMatrix) := by
  have h :
      gamma a * gamma a + gamma a * gamma a =
        (1 : GammaMatrix) + 1 := by
    simpa only [ite_true, two_smul] using (gamma_clifford a a)
  ext i j
  have hij := congrArg (fun M : GammaMatrix => M i j) h
  simp only [Matrix.add_apply] at hij
  linarith

/-- Original PUBLIC Clifford anticommutator, with the
original nine-source labels and original real gammas. -/
theorem source9OriginalGamma_anticommute
    (a b : SpaceIndex) (hab : a ≠ b) :
    gamma a * gamma b = -(gamma b * gamma a) := by
  have h := gamma_clifford a b
  simp only [ite_eq_right hab, zero_smul] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The trace of each ORIGINAL public real gamma basis
matrix is zero. Proof uses a distinct genuine gamma matrix
to conjugate gamma_a to -gamma_a; cyclic trace equality and
the exact gamma_b^2=I source identity force zero trace. -/
theorem source9OriginalGamma_basis_trace_zero
    (a : SpaceIndex) :
    Matrix.trace (gamma a) = 0 := by
  let b : SpaceIndex := if a = 0 then 1 else 0
  have hba : b ≠ a := by
    by_cases ha : a = 0
    · subst a
      change (1 : SpaceIndex) ≠ 0
      decide
    · simpa [b, ha] using (Ne.symm ha)
  have hsq : gamma b * gamma b = (1 : GammaMatrix) :=
    source9OriginalGamma_basis_mul_self b
  have hanti : gamma b * gamma a = -(gamma a * gamma b) :=
    source9OriginalGamma_anticommute b a hba
  have hconj : gamma b * gamma a * gamma b = -(gamma a) := by
    calc
      gamma b * gamma a * gamma b =
          -(gamma a * gamma b) * gamma b := by rw [hanti]
      _ = -(gamma a * (gamma b * gamma b)) := by
        rw [neg_mul, mul_assoc]
      _ = -(gamma a) := by rw [hsq, mul_one]
  have hcycle :
      Matrix.trace (gamma b * gamma a * gamma b) =
        Matrix.trace (gamma a) := by
    calc
      Matrix.trace ((gamma b * gamma a) * gamma b) =
          Matrix.trace (gamma b * (gamma b * gamma a)) :=
            Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((gamma b * gamma b) * gamma a) := by
        rw [← mul_assoc]
      _ = Matrix.trace (gamma a) := by rw [hsq, one_mul]
  have ht : Matrix.trace (gamma a) = -Matrix.trace (gamma a) := by
    calc
      Matrix.trace (gamma a) =
          Matrix.trace (gamma b * gamma a * gamma b) := hcycle.symm
      _ = -Matrix.trace (gamma a) := by rw [hconj, Matrix.trace_neg]
  linarith

/-- All ORIGINAL source-nine-vector gamma linear
combinations are traceless over ℝ, using the accepted
gammaNineRealLinear (NOT a replacement matrix family). -/
theorem gammaNineRealLinear_trace_zero
    (v : SpaceIndex → ℝ) :
    Matrix.trace (gammaNineRealLinear v) = 0 := by
  change Matrix.trace
    (∑ i : SpaceIndex, (v i) • gamma i) = 0
  rw [Matrix.trace_sum]
  simp [Matrix.trace_smul, source9OriginalGamma_basis_trace_zero]

#print axioms source9OriginalGamma_basis_mul_self
#print axioms source9OriginalGamma_anticommute
#print axioms source9OriginalGamma_basis_trace_zero
#print axioms gammaNineRealLinear_trace_zero

end
end FCP.BFSSPairedSpin9DetFixture
