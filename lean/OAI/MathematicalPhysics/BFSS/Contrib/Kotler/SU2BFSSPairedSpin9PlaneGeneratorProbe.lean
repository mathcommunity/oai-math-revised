import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2PairedThetaLabelCrosswalkProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V0StandaloneOrthogonalGeometryProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2RealGammaProbe
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
K1D18V8A — original paired-Fock 48-real Spin(9) plane matrices, algebraic interface.

This module uses the ACTUAL G1A pairedLabelEquiv, the ACTUAL original
Source48Label = Fin 24 × Fin 2, and the literal FCP.BFSSGamma9.gamma matrices.
It proves source-indexed skewness and the square -1 of the DOUBLED plane
generator -gamma_r gamma_s, for distinct spatial labels. The true Lie
generator has an additional factor 1/2; no Lie-group integration, continuous
Spin(9) lift, Clifford/Fock implementation, gauge theorem, or physical
Hamiltonian theorem is claimed.

A matrix reindexing equivalence is an exact typed index transport; it is NOT
an identification of the paired source basis with the color-major basis.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSPairedThetaLabelCrosswalk
open FCP.BFSSGamma9
open scoped Kronecker

/-- Exact source G1A paired label, with color first only on the intermediate
Kronecker product. Its codomain is the original Source48Label. -/
noncomputable def pairedColorSpinEquiv :
    (ColorIndex 2 × SpinIndex) ≃ Source48Label :=
  (Equiv.prodComm (ColorIndex 2) SpinIndex).trans pairedLabelEquiv

/-- The integer-normalized (doubled) nine-gamma plane matrix on the
actual source real sixteen-spinor index. -/
noncomputable def plane16 (r s : SpaceIndex) : GammaMatrix :=
  -(gamma r * gamma s)

/-- The doubled plane matrix, on the ACTUAL original paired-Fock 48 labels. -/
noncomputable def originalPairedPlane (r s : SpaceIndex) :
    Matrix Source48Label Source48Label ℝ :=
  (Matrix.reindexRingEquiv ℝ pairedColorSpinEquiv)
    ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 r s)

private theorem gamma_sq_one (r : SpaceIndex) :
    gamma r * gamma r = (1 : GammaMatrix) := by
  have h : gamma r * gamma r + gamma r * gamma r =
      (1 : GammaMatrix) + (1 : GammaMatrix) := by
    simpa only [eq_self, ite_true, two_smul] using
      (FCP.BFSSGamma9.gamma_clifford r r)
  ext i j
  have hij := congrArg (fun M : GammaMatrix => M i j) h
  simp only [Matrix.add_apply] at hij
  linarith

private theorem gamma_swap (r s : SpaceIndex) (hrs : r ≠ s) :
    gamma s * gamma r = -(gamma r * gamma s) := by
  have h : gamma r * gamma s + gamma s * gamma r = 0 := by
    simpa [hrs] using (FCP.BFSSGamma9.gamma_clifford r s)
  calc
    gamma s * gamma r =
        (gamma r * gamma s + gamma s * gamma r) - gamma r * gamma s := by
      abel
    _ = -(gamma r * gamma s) := by rw [h]; simp

private theorem plane16_transpose (r s : SpaceIndex) (hrs : r ≠ s) :
    (plane16 r s).transpose = -(plane16 r s) := by
  calc
    (plane16 r s).transpose = -(gamma s * gamma r) := by
      simp only [plane16, Matrix.transpose_neg, Matrix.transpose_mul]
      rw [FCP.BFSSGamma9.gamma_symmetric s,
        FCP.BFSSGamma9.gamma_symmetric r]
    _ = gamma r * gamma s := by rw [gamma_swap r s hrs]; simp
    _ = -(plane16 r s) := by simp [plane16]

private theorem plane16_sq (r s : SpaceIndex) (hrs : r ≠ s) :
    plane16 r s * plane16 r s = -(1 : GammaMatrix) := by
  calc
    plane16 r s * plane16 r s =
        (gamma r * gamma s) * (gamma r * gamma s) := by simp [plane16]
    _ = gamma r * (gamma s * gamma r) * gamma s := by
      simp only [mul_assoc]
    _ = gamma r * (-(gamma r * gamma s)) * gamma s := by
      rw [gamma_swap r s hrs]
    _ = -((gamma r * gamma r) * (gamma s * gamma s)) := by
      simp only [mul_neg, neg_mul, mul_assoc]
    _ = -(1 : GammaMatrix) := by
      rw [gamma_sq_one r, gamma_sq_one s, one_mul]

private theorem kroneckerPlane_transpose (r s : SpaceIndex) (hrs : r ≠ s) :
    (((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 r s).transpose) =
      -((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 r s) := by
  calc
    (((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 r s).transpose) =
        ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ).transpose) ⊗ₖ
          (plane16 r s).transpose := by
      exact (Matrix.kroneckerMap_transpose (· * ·)
        (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) (plane16 r s)).symm
    _ = (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ
        (-(plane16 r s)) := by
      rw [Matrix.transpose_one, plane16_transpose r s hrs]
    _ = -((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 r s) := by
      ext ⟨a, i⟩ ⟨b, j⟩
      simp only [Matrix.kronecker_apply, Matrix.neg_apply, mul_neg]

private theorem kroneckerPlane_sq (r s : SpaceIndex) (hrs : r ≠ s) :
    ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 r s) *
        ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 r s) =
      -(1 : Matrix (ColorIndex 2 × SpinIndex) (ColorIndex 2 × SpinIndex) ℝ) := by
  calc
    ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 r s) *
        ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 r s) =
      ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) *
        (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ)) ⊗ₖ
        (plane16 r s * plane16 r s) := by
      exact (Matrix.mul_kronecker_mul
        (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ)
        (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ)
        (plane16 r s) (plane16 r s)).symm
    _ = (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ
        (-(1 : GammaMatrix)) := by
      rw [one_mul, plane16_sq r s hrs]
    _ = -((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ
        (1 : GammaMatrix)) := by
      ext ⟨a, i⟩ ⟨b, j⟩
      simp only [Matrix.kronecker_apply, Matrix.neg_apply, mul_neg]
    _ = -(1 : Matrix (ColorIndex 2 × SpinIndex) (ColorIndex 2 × SpinIndex) ℝ) := by
      rw [Matrix.one_kronecker_one]

/-- Source-indexed doubled Spin(9) plane matrix is skew. -/
theorem originalPairedPlane_transpose (r s : SpaceIndex) (hrs : r ≠ s) :
    (originalPairedPlane r s).transpose = -(originalPairedPlane r s) := by
  let E := Matrix.reindexRingEquiv ℝ pairedColorSpinEquiv
  let B : Matrix (ColorIndex 2 × SpinIndex) (ColorIndex 2 × SpinIndex) ℝ :=
    (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 r s
  have htransport (M : Matrix (ColorIndex 2 × SpinIndex)
      (ColorIndex 2 × SpinIndex) ℝ) :
      (E M).transpose = E M.transpose := by
    ext p q
    rfl
  change (E B).transpose = -(E B)
  calc
    (E B).transpose = E B.transpose := htransport B
    _ = E (-B) := by
      exact congrArg E (kroneckerPlane_transpose r s hrs)
    _ = -(E B) := by rw [map_neg]

/-- Source-indexed doubled Spin(9) plane matrix squares to negative identity. -/
theorem originalPairedPlane_sq (r s : SpaceIndex) (hrs : r ≠ s) :
    originalPairedPlane r s * originalPairedPlane r s =
      -(1 : Matrix Source48Label Source48Label ℝ) := by
  let E := Matrix.reindexRingEquiv ℝ pairedColorSpinEquiv
  let B : Matrix (ColorIndex 2 × SpinIndex) (ColorIndex 2 × SpinIndex) ℝ :=
    (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 r s
  have h := congrArg E (kroneckerPlane_sq r s hrs)
  change E B * E B = -(1 : Matrix Source48Label Source48Label ℝ)
  simpa only [map_mul, map_neg, map_one] using h

#print axioms originalPairedPlane_transpose
#print axioms originalPairedPlane_sq

end
end FCP.BFSSPairedSpin9Plane
