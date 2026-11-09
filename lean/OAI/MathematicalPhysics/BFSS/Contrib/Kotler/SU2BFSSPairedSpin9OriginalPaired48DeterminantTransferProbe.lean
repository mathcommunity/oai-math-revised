import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9SourceSpinOriginalPaired48OrthogonalProbe
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
K1D18V10G — exact determinant transfer and conditional
SO(original paired 48) membership from the genuinely
qualified V10F source Spin9 → O(original paired 48).

Pinned Mathlib:
- Matrix.det_reindex_self: same row/column Fock-label
  permutation preserves determinant.
- Matrix.det_kronecker: determinant of the ACTUAL
  three-color identity tensor 16-real spinor matrix.

This tests the exact equality det(I₃ ⊗ A) = det(A)^3,
not an invented determinant-one proof for original Spin9.

CANDIDATE UNTIL STRICT COMPILER AND INDEPENDENT AXIOM GATE.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSPairedSpin9Plane
open FCP.BFSSGamma9
open Matrix
open scoped Kronecker

/-- The exact original Fock-paired 48-label determinant is
the cube of the original 16-spinor determinant, because
there are THREE source color labels and the actual G1A
paired permutation changes rows and columns together. -/
theorem gamma16ToOriginalPaired48_det (A : GammaMatrix) :
    (gamma16ToOriginalPaired48 A).det = A.det ^ 3 := by
  let E := Matrix.reindexRingEquiv ℝ pairedColorSpinEquiv
  let B : Matrix (ColorIndex 2 × SpinIndex)
      (ColorIndex 2 × SpinIndex) ℝ :=
    (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ A
  have hdet (M : Matrix (ColorIndex 2 × SpinIndex)
      (ColorIndex 2 × SpinIndex) ℝ) :
      (E M).det = M.det := by
    change (Matrix.reindex pairedColorSpinEquiv pairedColorSpinEquiv M).det =
      M.det
    exact Matrix.det_reindex_self pairedColorSpinEquiv M
  change (E B).det = A.det ^ 3
  calc
    (E B).det = B.det := hdet B
    _ = ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ).det) ^
          Fintype.card SpinIndex * A.det ^ Fintype.card (ColorIndex 2) :=
      Matrix.det_kronecker _ _
    _ = A.det ^ 3 := by
      norm_num [ColorIndex, colorDim]

/-- The source Spin9 global O(48) determinant is exactly the
cube of its original Clifford gamma O(16) determinant.
Neither side is assumed +1. -/
theorem source9SpinOriginalPaired48OrthogonalHom_det
    (g : spinGroup source9Quadratic) :
    (((source9SpinOriginalPaired48OrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ)).det =
      (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) ^ 3 := by
  exact gamma16ToOriginalPaired48_det
    ((source9SpinGammaOrthogonalHom g) : GammaMatrix)

/-- Actual source doubled-plane matrix is EXACTLY the same
48-label transport now used by the global source-group action,
rather than the rejected old color-major matrix. -/
theorem gamma16ToOriginalPaired48_plane (r s : SpaceIndex) :
    gamma16ToOriginalPaired48 (plane16 r s) =
      originalPairedPlane r s := rfl

/-- Conditional orientation bridge. A proof that the 16-real
source gamma Spin9 image has determinant +1 suffices to
promote its *actual original paired-48* image from O(48)
to SO(48). This does NOT prove that antecedent. -/
theorem source9SpinOriginalPaired48_mem_specialOrthogonal_of_gamma_det_one
    (g : spinGroup source9Quadratic)
    (hdet :
      (((source9SpinGammaOrthogonalHom g) : GammaMatrix)).det = 1) :
    ((source9SpinOriginalPaired48OrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ) ∈
      Matrix.specialOrthogonalGroup Source48Label ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · exact (source9SpinOriginalPaired48OrthogonalHom g).property
  · rw [source9SpinOriginalPaired48OrthogonalHom_det, hdet]
    norm_num

#print axioms gamma16ToOriginalPaired48_det
#print axioms source9SpinOriginalPaired48OrthogonalHom_det
#print axioms gamma16ToOriginalPaired48_plane
#print axioms source9SpinOriginalPaired48_mem_specialOrthogonal_of_gamma_det_one

end
end FCP.BFSSPairedSpin9Clifford
