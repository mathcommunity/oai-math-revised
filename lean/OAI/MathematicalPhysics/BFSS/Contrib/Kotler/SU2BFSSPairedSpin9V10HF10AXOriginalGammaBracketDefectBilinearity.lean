import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10AWOriginalGammaCoordinatePlaneBracketCompatibility

/-!
K1D18V10H-F10AX — typed real bilinearity of the
original-16 gamma bracket-preservation defect.

F10AV qualified the exact real coefficient LinearMap
  rho(A) = (1/4) sum_{r,s} A_rs gamma_r gamma_s
from native real 9x9 matrices to the original real 16x16
gamma carrier. F10AW qualified its commutator preservation
on every pair of source-native coordinate planes.

This stage defines the raw matrix defect
  D(A,B) = rho(A*B-B*A) - (rho(A)*rho(B)-rho(B)*rho(A))
and proves only additivity and real scalar homogeneity in
each input for arbitrary native source matrices.

No skew hypothesis is imposed. Generator-pair zero,
finite-sum extension to arbitrary skew pairs, a typed
so(9) -> so(16) LieHom, global Spin(9) integration,
Spin(48), Fock, gauge, physical-domain, and BFSS spectral
claims remain separate obligations.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSPairedSpin9DetFixture
open OAI.BFSSQuantum
open Matrix

/-- The exact failure of the original-16 gamma coefficient
LinearMap to preserve native 9x9 matrix commutators. -/
noncomputable def coordinateToOriginalGammaBracketDefect
    (A B : Matrix SpaceIndex SpaceIndex ℝ) : GammaMatrix :=
  coordinateToOriginalGammaLinearMap (A * B - B * A) -
    (coordinateToOriginalGammaLinearMap A *
        coordinateToOriginalGammaLinearMap B -
      coordinateToOriginalGammaLinearMap B *
        coordinateToOriginalGammaLinearMap A)

/-- Additivity of the original-gamma bracket defect in its
first native source-matrix argument. -/
theorem coordinateToOriginalGammaBracketDefect_add_left
    (A B C : Matrix SpaceIndex SpaceIndex ℝ) :
    coordinateToOriginalGammaBracketDefect (A + B) C =
      coordinateToOriginalGammaBracketDefect A C +
        coordinateToOriginalGammaBracketDefect B C := by
  unfold coordinateToOriginalGammaBracketDefect
  simp only [add_mul, mul_add, map_add, map_sub]
  abel

/-- Additivity of the original-gamma bracket defect in its
second native source-matrix argument. -/
theorem coordinateToOriginalGammaBracketDefect_add_right
    (A B C : Matrix SpaceIndex SpaceIndex ℝ) :
    coordinateToOriginalGammaBracketDefect A (B + C) =
      coordinateToOriginalGammaBracketDefect A B +
        coordinateToOriginalGammaBracketDefect A C := by
  unfold coordinateToOriginalGammaBracketDefect
  simp only [add_mul, mul_add, map_add, map_sub]
  abel

/-- Real homogeneity of the original-gamma bracket defect
in its first native source-matrix argument. -/
theorem coordinateToOriginalGammaBracketDefect_smul_left
    (c : ℝ) (A B : Matrix SpaceIndex SpaceIndex ℝ) :
    coordinateToOriginalGammaBracketDefect (c • A) B =
      c • coordinateToOriginalGammaBracketDefect A B := by
  unfold coordinateToOriginalGammaBracketDefect
  simp only [smul_mul_assoc, mul_smul_comm,
    map_smul, map_sub, smul_sub]

/-- Real homogeneity of the original-gamma bracket defect
in its second native source-matrix argument. -/
theorem coordinateToOriginalGammaBracketDefect_smul_right
    (c : ℝ) (A B : Matrix SpaceIndex SpaceIndex ℝ) :
    coordinateToOriginalGammaBracketDefect A (c • B) =
      c • coordinateToOriginalGammaBracketDefect A B := by
  unfold coordinateToOriginalGammaBracketDefect
  simp only [smul_mul_assoc, mul_smul_comm,
    map_smul, map_sub, smul_sub]

#print axioms coordinateToOriginalGammaBracketDefect
#print axioms coordinateToOriginalGammaBracketDefect_add_left
#print axioms coordinateToOriginalGammaBracketDefect_add_right
#print axioms coordinateToOriginalGammaBracketDefect_smul_left
#print axioms coordinateToOriginalGammaBracketDefect_smul_right

end
end FCP.BFSSPairedSpin9Clifford
