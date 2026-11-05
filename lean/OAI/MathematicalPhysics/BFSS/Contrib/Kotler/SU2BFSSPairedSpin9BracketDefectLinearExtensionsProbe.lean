import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9BracketDefectScalarProbe

/-!
K1D18V9K — exact bilinear defect packaging and zero on original
native coordinate-generator pairs.

V9I and V9J strictly prove additivity and real homogeneity
for each argument of D. Bundle the exact maps while one argument
is fixed to make finite-sum transport source-exact.

The original paired 48-real output labels and native source 9-index
matrices are unchanged. This gate proves D(F_rs,F_tu)=0, not yet
D(A,B)=0 for arbitrary skew input A and B.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0

/-- The bracket defect is a genuine real linear map in its second
argument for each fixed source-native nine-index input matrix. -/
noncomputable def coordinateToPairedBracketDefect_rightLinear
    (A : Matrix SpaceIndex SpaceIndex ℝ) :
    Matrix SpaceIndex SpaceIndex ℝ →ₗ[ℝ]
      Matrix Source48Label Source48Label ℝ where
  toFun := coordinateToPairedBracketDefect A
  map_add' := coordinateToPairedBracketDefect_add_right A
  map_smul' := fun c B => coordinateToPairedBracketDefect_smul_right c A B

/-- The bracket defect is a genuine real linear map in its first
argument for each fixed source-native nine-index input matrix. -/
noncomputable def coordinateToPairedBracketDefect_leftLinear
    (B : Matrix SpaceIndex SpaceIndex ℝ) :
    Matrix SpaceIndex SpaceIndex ℝ →ₗ[ℝ]
      Matrix Source48Label Source48Label ℝ where
  toFun := fun A => coordinateToPairedBracketDefect A B
  map_add' := fun A C => coordinateToPairedBracketDefect_add_left A C B
  map_smul' := fun c A => coordinateToPairedBracketDefect_smul_left c A B

/-- Exact original paired 48-real defect vanishes on every two
native source coordinate generators, including all index collisions. -/
theorem coordinateToPairedBracketDefect_coordinatePlanes
    (r s t u : SpaceIndex) :
    coordinateToPairedBracketDefect
      (coordinatePlane9 r s) (coordinatePlane9 t u) = 0 := by
  simp only [coordinateToPairedBracketDefect,
    coordinateToPairedLinearMap_generator_commutator, sub_self]

#print axioms coordinateToPairedBracketDefect_coordinatePlanes

end
end FCP.BFSSPairedSpin9Plane
