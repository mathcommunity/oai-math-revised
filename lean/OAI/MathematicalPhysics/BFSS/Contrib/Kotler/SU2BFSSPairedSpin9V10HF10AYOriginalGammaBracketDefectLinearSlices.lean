import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10AXOriginalGammaBracketDefectBilinearity

/-!
K1D18V10H-F10AY — typed linear slices of the
original-16 gamma bracket defect and exact zero on every
source-native coordinate-plane pair.

F10AX qualified additivity and real scalar homogeneity of
the exact raw defect in both source-matrix inputs. Package
those laws as real LinearMaps with one input fixed. Then use
accepted F10AW generator-pair commutator preservation to
prove D(F_rs,F_tu)=0 for all four source labels, including
diagonal and every collision case.

This stage does not extend the zero theorem to an arbitrary
skew input. One-plane-versus-skew, arbitrary-skew-pair
vanishing, a typed so(9) -> so(16) LieHom, group integration,
Spin(48), Fock, gauge, physical-domain, and BFSS spectral
claims remain separate obligations.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSPairedSpin9DetFixture
open FCP.BFSSPairedSpin9Plane
open OAI.BFSSQuantum
open Matrix

/-- For each fixed first source matrix, the exact
original-gamma bracket defect is a real LinearMap in its
second source-matrix input. -/
noncomputable def coordinateToOriginalGammaBracketDefect_rightLinear
    (A : Matrix SpaceIndex SpaceIndex ℝ) :
    Matrix SpaceIndex SpaceIndex ℝ →ₗ[ℝ] GammaMatrix where
  toFun := coordinateToOriginalGammaBracketDefect A
  map_add' := coordinateToOriginalGammaBracketDefect_add_right A
  map_smul' := fun c B =>
    coordinateToOriginalGammaBracketDefect_smul_right c A B

/-- For each fixed second source matrix, the exact
original-gamma bracket defect is a real LinearMap in its
first source-matrix input. -/
noncomputable def coordinateToOriginalGammaBracketDefect_leftLinear
    (B : Matrix SpaceIndex SpaceIndex ℝ) :
    Matrix SpaceIndex SpaceIndex ℝ →ₗ[ℝ] GammaMatrix where
  toFun := fun A => coordinateToOriginalGammaBracketDefect A B
  map_add' := fun A C =>
    coordinateToOriginalGammaBracketDefect_add_left A C B
  map_smul' := fun c A =>
    coordinateToOriginalGammaBracketDefect_smul_left c A B

/-- The exact original-gamma bracket defect vanishes on
every pair of source-native coordinate planes, including
all diagonal and source-label collision cases. -/
theorem coordinateToOriginalGammaBracketDefect_coordinatePlanes
    (r s t u : SpaceIndex) :
    coordinateToOriginalGammaBracketDefect
      (coordinatePlane9 r s) (coordinatePlane9 t u) = 0 := by
  simp only [coordinateToOriginalGammaBracketDefect,
    coordinateToOriginalGammaLinearMap_coordinatePlane_bracket,
    sub_self]

#print axioms coordinateToOriginalGammaBracketDefect_rightLinear
#print axioms coordinateToOriginalGammaBracketDefect_leftLinear
#print axioms coordinateToOriginalGammaBracketDefect_coordinatePlanes

end
end FCP.BFSSPairedSpin9Clifford
