import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10AZOriginalGammaBracketDefectPlaneSkewExtension

/-!
K1D18V10H-F10BA — exact second finite-sum extension
of original-16 gamma bracket-defect zero.

F10AZ qualified zero for any source-native coordinate
plane against an arbitrary skew second input. Apply the
accepted left-linear defect slice to V9F's exact
ordered-pair expansion of an arbitrary skew first input.
This proves defect zero for every pair of skew native real
9x9 source matrices.

The theorem retains the original 16x16 gamma target. A
typed so(9) -> so(16) LieHom, group integration, Spin(48),
Fock, gauge, physical-domain, and BFSS spectral claims
remain separate.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSPairedSpin9DetFixture
open FCP.BFSSPairedSpin9Plane
open OAI.BFSSQuantum
open Matrix
open scoped BigOperators

/-- The original-gamma bracket defect vanishes for every
pair of skew native real 9x9 source matrices. -/
theorem coordinateToOriginalGammaBracketDefect_skew_pair_zero
    (A B : Matrix SpaceIndex SpaceIndex ℝ)
    (hA : A.transpose = -A)
    (hB : B.transpose = -B) :
    coordinateToOriginalGammaBracketDefect A B = 0 := by
  let L : Matrix SpaceIndex SpaceIndex ℝ →ₗ[ℝ] GammaMatrix :=
    coordinateToOriginalGammaBracketDefect_leftLinear B
  have hzero (r s : SpaceIndex) :
      L (coordinatePlane9 r s) = 0 :=
    coordinateToOriginalGammaBracketDefect_plane_skew_right r s B hB
  change L A = 0
  rw [coordinateSkewMatrix9_plane_spanning A hA]
  simp only [map_smul, map_sum, hzero, smul_zero,
    Finset.sum_const_zero]

#print axioms coordinateToOriginalGammaBracketDefect_skew_pair_zero

end
end FCP.BFSSPairedSpin9Clifford
