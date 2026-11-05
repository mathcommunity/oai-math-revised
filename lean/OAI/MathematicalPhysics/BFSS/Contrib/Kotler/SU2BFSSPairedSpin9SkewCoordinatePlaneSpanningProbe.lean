import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9AntisymmetricPartExpansionProbe

/-!
K1D18V9F — true native nine-index skew-matrix spanning by
the exact antisymmetric coordinate planes.

For each real A : Matrix SpaceIndex SpaceIndex ℝ with A.transpose=-A,
V9E's all-input antisymmetric-part identity specializes to a
half-scaled finite sum over all ordered spatial pairs.

The coefficient (1/2:ℝ), pair order, diagonal coincidences and exact
source-native SpaceIndex are retained, without a color-major basis
substitution or a claim of arbitrary Lie bracket preservation.

Full bracket preservation, LieHom construction, global Spin(9) lift
and BFSS physical claims remain separate unproved obligations.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open scoped BigOperators

/-- Every real skew nine-index source matrix is a full finite real
linear combination of the original native coordinate planes,
with the exact ordered-pair one-half normalization. -/
theorem coordinateSkewMatrix9_plane_spanning
    (A : Matrix SpaceIndex SpaceIndex ℝ)
    (hA : A.transpose = -A) :
    A = (1 / 2 : ℝ) •
      (∑ r : SpaceIndex, ∑ s : SpaceIndex,
        (A r s) • coordinatePlane9 r s) := by
  rw [coordinateMatrix9_antisymmetric_part_expansion A, hA]
  ext i j
  change A i j = (1 / 2 : ℝ) * (A i j - -(A i j))
  ring

#print axioms coordinateSkewMatrix9_plane_spanning

end
end FCP.BFSSPairedSpin9Plane
