import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9BracketDefectPlaneSkewExtensionProbe

/-!
K1D18V9M — source-native arbitrary skew-pair commutator-defect
vanishing for the accepted nine-to-original-Fock-paired-48
real LinearMap.

Using accepted V9F full ordered-pair skew spanning, V9K's genuine
first-input real-linear defect slice and V9L's zero on any source
coordinate generator against an arbitrary skew second argument,
prove the full defect vanishes on every two skew source matrices.

This is the native matrix commutator-preservation equality, not
yet a structure-level LieHom, global Spin(9) integration, or BFSS
physical/spectral existence claim.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open scoped BigOperators

/-- For any two real skew source-native nine-index matrices the
original paired-Fock 48-real coefficient map preserves the
actual matrix product commutator, expressed as zero defect. -/
theorem coordinateToPairedBracketDefect_skew_pair_zero
    (A B : Matrix SpaceIndex SpaceIndex ℝ)
    (hA : A.transpose = -A)
    (hB : B.transpose = -B) :
    coordinateToPairedBracketDefect A B = 0 := by
  let L : Matrix SpaceIndex SpaceIndex ℝ →ₗ[ℝ]
      Matrix Source48Label Source48Label ℝ :=
    coordinateToPairedBracketDefect_leftLinear B
  have hzero (r s : SpaceIndex) : L (coordinatePlane9 r s) = 0 :=
    coordinateToPairedBracketDefect_plane_skew_right r s B hB
  change L A = 0
  rw [coordinateSkewMatrix9_plane_spanning A hA]
  simp only [map_smul, map_sum, hzero, smul_zero,
    Finset.sum_const_zero]

#print axioms coordinateToPairedBracketDefect_skew_pair_zero

end
end FCP.BFSSPairedSpin9Plane
