import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9NormalizedAdjacentBracketProbe

/-!
K1D18V8Q — original paired-Fock 48-real universal scalar-normalized
Spin(9) commutator bridge.

The accepted V8M source-L commutator is valid for all index coincidences.
The accepted V8O normalization H=-1/2 • L is extended to the full
four-index bracket using the V8P typed matrix scalar transport.

This module proves only [H_rs,H_tu] = (1/4) • originalFourIndexRHS.
It does NOT yet prove the explicit four-Kronecker-delta formula written
in normalized H or a Lie algebra linear extension to all skew matrices.
No group action, source Majorana operator or BFSS spectral claims.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum

/-- For every four spatial indices, the normalized commutator is one
quarter of the exact original source-L four-index right-hand side. -/
theorem normalizedPairedPlane_universal_scalar_bracket
    (r s t u : SpaceIndex) :
    normalizedPairedPlane r s * normalizedPairedPlane t u -
      normalizedPairedPlane t u * normalizedPairedPlane r s =
    (1 / 4 : ℝ) • zeroDiagonalFourIndexRHS r s t u := by
  unfold normalizedPairedPlane
  calc
    ((-(1 / 2 : ℝ)) • zeroDiagonalPairedPlane r s) *
        ((-(1 / 2 : ℝ)) • zeroDiagonalPairedPlane t u) -
        ((-(1 / 2 : ℝ)) • zeroDiagonalPairedPlane t u) *
          ((-(1 / 2 : ℝ)) • zeroDiagonalPairedPlane r s) =
      ((-(1 / 2 : ℝ)) * (-(1 / 2 : ℝ))) •
        (zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane t u -
          zeroDiagonalPairedPlane t u * zeroDiagonalPairedPlane r s) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub]
    _ = ((-(1 / 2 : ℝ)) * (-(1 / 2 : ℝ))) •
        zeroDiagonalFourIndexRHS r s t u := by
      rw [zeroDiagonalFourIndex_universal_bracket r s t u]
    _ = (1 / 4 : ℝ) • zeroDiagonalFourIndexRHS r s t u := by
      congr 1
      ring

#print axioms normalizedPairedPlane_universal_scalar_bracket

end
end FCP.BFSSPairedSpin9Plane
