import OAI.MathematicalPhysics.BFSS.Core

/-!
L9E5B0 — STAGED, UNQUALIFIED exact real-to-complex scalar
compatibility of the genuine original Fermion 2 complex-linear
continuous endomorphisms.

L9E5A Gate #1 and #2 prove this is NOT discharged by guessing
IsScalarTower ℝ FockOp FockOp or by one generic top-level
Complex.coe_smul simp. The intended proof is extensional on the
original Fock vector and must preserve the actual original
ContinuousLinearMap scalar instances. A strict gate, with exact
source pins and #print axioms, remains REQUIRED. This is not
a constructed Clifford representation or BFSS square theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 280000

namespace FCP.BFSSS1V52L9E5B0
noncomputable section

open OAI.BFSSQuantum

private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- Bridging the REAL source coefficient action to the native
COMPLEX multiplication action on the same original Fock operator.
No surrogate operator module or axiom is introduced. -/
theorem originalFockOperator_real_smul_eq_complex_smul
    (a : ℝ) (T : FockOp) :
    a • T = (a : ℂ) • T := by
  -- Gate #1's broad `ext ψ` over-expanded into PiLp coordinates.
  -- Stop specifically at ContinuousLinearMap extensionality.
  apply ContinuousLinearMap.ext
  intro ψ
  simp only [smul_apply]
  exact (Complex.coe_smul a (T ψ)).symm

#print axioms originalFockOperator_real_smul_eq_complex_smul

end
end FCP.BFSSS1V52L9E5B0
