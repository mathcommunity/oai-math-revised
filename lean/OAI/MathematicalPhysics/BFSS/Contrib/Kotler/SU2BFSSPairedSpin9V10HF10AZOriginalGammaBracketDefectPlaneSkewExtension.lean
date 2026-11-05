import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10AYOriginalGammaBracketDefectLinearSlices

/-!
K1D18V10H-F10AZ — exact first finite-sum extension
of original-16 gamma bracket-defect zero.

F10AY qualified the right-linear defect slice and zero on
every pair of source-native coordinate planes. Apply that
LinearMap to V9F's exact ordered-pair expansion of an
arbitrary skew real 9x9 source matrix. This proves zero for
one fixed coordinate plane against an arbitrary skew second
input.

The theorem retains the original 16x16 gamma target. Full
arbitrary-skew-pair vanishing, a typed so(9) -> so(16)
LieHom, group integration, Spin(48), Fock, gauge,
physical-domain, and BFSS spectral claims remain separate.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSPairedSpin9DetFixture
open FCP.BFSSPairedSpin9Plane
open OAI.BFSSQuantum
open Matrix
open scoped BigOperators

/-- The original-gamma bracket defect vanishes on any
source-native coordinate plane in the first input and any
skew native real 9x9 matrix in the second input. -/
theorem coordinateToOriginalGammaBracketDefect_plane_skew_right
    (r s : SpaceIndex)
    (B : Matrix SpaceIndex SpaceIndex ℝ)
    (hB : B.transpose = -B) :
    coordinateToOriginalGammaBracketDefect
      (coordinatePlane9 r s) B = 0 := by
  let L : Matrix SpaceIndex SpaceIndex ℝ →ₗ[ℝ] GammaMatrix :=
    coordinateToOriginalGammaBracketDefect_rightLinear
      (coordinatePlane9 r s)
  have hzero (t u : SpaceIndex) :
      L (coordinatePlane9 t u) = 0 :=
    coordinateToOriginalGammaBracketDefect_coordinatePlanes r s t u
  change L B = 0
  rw [coordinateSkewMatrix9_plane_spanning B hB]
  simp only [map_smul, map_sum, hzero, smul_zero,
    Finset.sum_const_zero]

#print axioms coordinateToOriginalGammaBracketDefect_plane_skew_right

end
end FCP.BFSSPairedSpin9Clifford
