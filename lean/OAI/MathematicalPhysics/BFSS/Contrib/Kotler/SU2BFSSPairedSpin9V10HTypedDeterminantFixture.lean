import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9OriginalPaired48DeterminantTransferProbe
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
K1D18V10H-F1 — ISOLATED TYPED COMPILER FIXTURE.

Two consecutive V10H full-module gate failures revealed:
(1) incorrect projection/implicit-argument elaboration of
    Matrix.mem_orthogonalGroup_iff;
(2) recursive delta reduction of a composed determinant
    MonoidHom from the original source Spin9 group.

This tiny fixture imports only ACCEPTED V10G ancestry.
It does NOT import, repair, or qualify broken V10H.
It proves two independent exact mathematical obligations
directly from the accepted source matrix representation:

- determinant squared is 1 for a source orthogonal gamma16;
- det(original G1A paired 48) = det(original gamma16).

No invented determinant-one theorem, continuity,
source Spin48 lift, or BFSS physical statement.
The original strict compiler gate must still verify it.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- Isolate the actual source subgroup orthogonality
as a typed proposition before using the Matrix iff.
Avoid the incorrectly unapplied `iff.mp` projection. -/
theorem gammaDetSquareOne
    (g : spinGroup source9Quadratic) :
    ((((source9SpinGammaOrthogonalHom g) : GammaMatrix).det)) ^ 2 = 1 := by
  have horth :
      ((source9SpinGammaOrthogonalHom g) : GammaMatrix) ∈
        Matrix.orthogonalGroup SpinIndex ℝ :=
    (source9SpinGammaOrthogonalHom g).property
  rw [Matrix.mem_orthogonalGroup_iff] at horth
  have hdet := congrArg Matrix.det horth
  have hdet_mul :
      (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) *
        (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_one] using hdet
  simpa only [pow_two] using hdet_mul

/-- Source-exact sign reduction with no determinant-character
MonoidHom elaboration: the qualified V10G cube formula and
orthogonality suffice. This is still not det = +1. -/
theorem pairedDetEqualGamma
    (g : spinGroup source9Quadratic) :
    (((source9SpinOriginalPaired48OrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ)).det =
      (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) := by
  calc
    (((source9SpinOriginalPaired48OrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ)).det =
        (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) ^ 3 :=
      source9SpinOriginalPaired48OrthogonalHom_det g
    _ = (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) ^ 2 *
        (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) := by ring
    _ = (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) := by
      rw [gammaDetSquareOne g, one_mul]

#print axioms gammaDetSquareOne
#print axioms pairedDetEqualGamma

end
end FCP.BFSSPairedSpin9DetFixture
