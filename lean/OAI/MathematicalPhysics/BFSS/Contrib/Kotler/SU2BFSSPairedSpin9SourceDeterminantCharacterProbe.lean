import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9OriginalPaired48DeterminantTransferProbe
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
K1D18V10H — an exact determinant character and
orientation-iff reduction for the genuinely qualified
source Spin(9) action on the original paired-Fock 48 labels.

The source determinant character is a group homomorphism
to real multiplicative values (it has values ±1), not a
proof of its triviality. The key independent identity is
det(A)^2 = 1 for every exact O(16) image. Combining with
the accepted V10G cube law yields det48 = det16.

A global SO48 homomorphism has NOT yet been constructed.
The genuinely missing source determinant-one obligation
remains OPEN. No invented group topology or Lie integration.
CANDIDATE until strict CI independent axiom gate passes.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open Matrix

/-- The determinant of the genuine global source Spin9
orthogonal 16-spinor representation is a multiplicative
character into the real multiplicative monoid. It is NOT
assumed to be the trivial character. -/
noncomputable def source9SpinGammaDetHom :
    spinGroup source9Quadratic →* ℝ :=
  (Matrix.detMonoidHom : GammaMatrix →* ℝ).comp
    ((Matrix.orthogonalGroup SpinIndex ℝ).subtype.comp
      source9SpinGammaOrthogonalHom)

/-- Explicit source-exact evaluation of the determinant
character, isolating the MonoidHom and Submonoid subtype
bridge before any orientation arithmetic. -/
theorem source9SpinGammaDetHom_apply
    (g : spinGroup source9Quadratic) :
    source9SpinGammaDetHom g =
      (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) := rfl

/-- Every genuine orthogonal source gamma image has
determinant square exactly one; orientation sign remains
undetermined by this equality alone. -/
theorem source9SpinGammaDetHom_sq
    (g : spinGroup source9Quadratic) :
    (source9SpinGammaDetHom g) ^ 2 = 1 := by
  have horth :
      ((source9SpinGammaOrthogonalHom g) : GammaMatrix) *
        ((source9SpinGammaOrthogonalHom g) : GammaMatrix).transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff).mp
      (source9SpinGammaOrthogonalHom g).property
  have hdet := congrArg Matrix.det horth
  have hdet_sq :
      (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) *
        (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_one] using hdet
  rw [source9SpinGammaDetHom_apply, pow_two]
  exact hdet_sq

/-- On the ACTUAL original paired 48 indices, the group
action determinant is exactly the 16-spinor determinant:
the odd color multiplicity 3 and orthogonality reduce
the qualified V10G cube law without asserting +1. -/
theorem source9SpinOriginalPaired48_det_eq_gamma
    (g : spinGroup source9Quadratic) :
    (((source9SpinOriginalPaired48OrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ)).det =
      (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) := by
  calc
    (((source9SpinOriginalPaired48OrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ)).det =
        (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) ^ 3 :=
      source9SpinOriginalPaired48OrthogonalHom_det g
    _ = (source9SpinGammaDetHom g) ^ 3 := by
      rw [source9SpinGammaDetHom_apply]
    _ = source9SpinGammaDetHom g := by
      calc
        (source9SpinGammaDetHom g) ^ 3 =
            (source9SpinGammaDetHom g) ^ 2 *
              source9SpinGammaDetHom g := by ring
        _ = source9SpinGammaDetHom g := by
          rw [source9SpinGammaDetHom_sq g, one_mul]
    _ = (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) :=
      source9SpinGammaDetHom_apply g

/-- The exact original paired 48-dimensional source action
has determinant +1 if and only if its original 16-spinor
source image has determinant +1. Neither is asserted
unconditionally, so the remaining obstruction is explicit. -/
theorem source9SpinOriginalPaired48_mem_specialOrthogonal_iff_gamma_det_one
    (g : spinGroup source9Quadratic) :
    ((source9SpinOriginalPaired48OrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ) ∈
      Matrix.specialOrthogonalGroup Source48Label ℝ ↔
      (((source9SpinGammaOrthogonalHom g) : GammaMatrix)).det = 1 := by
  constructor
  · intro h
    have hdet :
        (((source9SpinOriginalPaired48OrthogonalHom g) :
          Matrix Source48Label Source48Label ℝ)).det = 1 :=
      ((Matrix.mem_specialOrthogonalGroup_iff).mp h).2
    rw [source9SpinOriginalPaired48_det_eq_gamma] at hdet
    exact hdet
  · intro h
    exact
      source9SpinOriginalPaired48_mem_specialOrthogonal_of_gamma_det_one
        g h

#print axioms source9SpinGammaDetHom
#print axioms source9SpinGammaDetHom_apply
#print axioms source9SpinGammaDetHom_sq
#print axioms source9SpinOriginalPaired48_det_eq_gamma
#print axioms source9SpinOriginalPaired48_mem_specialOrthogonal_iff_gamma_det_one

end
end FCP.BFSSPairedSpin9Clifford
