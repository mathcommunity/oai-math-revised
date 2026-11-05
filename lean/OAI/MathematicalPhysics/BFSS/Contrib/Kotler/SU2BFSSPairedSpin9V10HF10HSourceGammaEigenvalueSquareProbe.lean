import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10GSourceGammaRealSpectralBridgeProbe
import Mathlib.Algebra.Module.Torsion.Free

/-!
K1D18V10H-F10H: source-exact eigenvalue SQUARE, using
the pinned REAL Hermitian spectral theorem, source exact
gammaNineRealLinear_sq, and a genuinely nonzero source
eigenvector. No matrix-private signed permutation access.

F9 (source determinant magnitude), F10E (trace zero),
F10F (Q positive and gamma symmetric) and F10G (exact
real eigenvalues and determinant/trace spectral bridges)
are qualified and immutable.

This candidate shows for every original nine-vector v and
every ORIGINAL spinor label i : Fin16,
  (eigenvalue_i Γ(v))^2 = source9Quadratic v,
and each eigenvalue is nonzero for v != 0.

Do NOT infer eight of each sign, positive determinant,
source Spin9 orientation, original SO48 or Spin48 lift.
All require independent proof obligations and strict gates.

F10H is NOT qualified until pinned warning-as-error
compilation, independent exact declaration types, and
root axiom whitelist pass. Failed private-table F10/F10D
probes remain red and are not imported into this module.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix
open WithLp

/-- A source-exact original gamma spectral eigenvalue
squares to the SOURCE quadratic form, not a substituted
norm or Clifford representation. -/
theorem gammaNineRealLinear_realEigenvalues_mul_self
    (v : SpaceIndex → ℝ) (i : SpinIndex) :
    (gammaNineRealLinear_isHermitian v).eigenvalues i *
        (gammaNineRealLinear_isHermitian v).eigenvalues i =
      source9Quadratic v := by
  let A : GammaMatrix := gammaNineRealLinear v
  let hA : A.IsHermitian := gammaNineRealLinear_isHermitian v
  let e : ℝ := hA.eigenvalues i
  let u : SpinIndex → ℝ := ⇑(hA.eigenvectorBasis i)
  have hu : u ≠ 0 := by
    dsimp [u]
    exact (ofLp_eq_zero 2).ne.2
      (hA.eigenvectorBasis.orthonormal.ne_zero i)
  have he : A *ᵥ u = e • u := by
    exact hA.mulVec_eigenvectorBasis i
  have hleft : (A * A) *ᵥ u = (e * e) • u := by
    rw [← Matrix.mulVec_mulVec, he, Matrix.mulVec_smul, he, smul_smul]
  have hright : (A * A) *ᵥ u = (source9Quadratic v) • u := by
    have hsq := gammaNineRealLinear_sq v
    change A * A = (source9Quadratic v) • (1 : GammaMatrix) at hsq
    rw [hsq, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hscalar : e * e = source9Quadratic v :=
    smul_left_injective ℝ hu (hleft.symm.trans hright)
  exact hscalar

/-- Every REAL eigenvalue of the original gamma16 is
nonzero for every NONZERO original nine-vector. This
uses the ACCEPTED positive-definite original Q. -/
theorem gammaNineRealLinear_realEigenvalues_ne_zero
    (v : SpaceIndex → ℝ) (hv : v ≠ 0)
    (i : SpinIndex) :
    (gammaNineRealLinear_isHermitian v).eigenvalues i ≠ 0 := by
  intro hzero
  have hmul := gammaNineRealLinear_realEigenvalues_mul_self v i
  have hQ : source9Quadratic v = 0 := by
    simpa [hzero] using hmul.symm
  exact hv ((source9Quadratic_eq_zero_iff v).mp hQ)

#print axioms gammaNineRealLinear_realEigenvalues_mul_self
#print axioms gammaNineRealLinear_realEigenvalues_ne_zero

end
end FCP.BFSSPairedSpin9DetFixture
