import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G4BOriginalCoefficientCommutatorProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G2OriginalHomogeneousRowFierzProbe

/-!
# L6G5A — original-source kinetic gamma Gram contraction

A small, source-faithful first component of the Hamiltonian–Gauss bridge.
The gamma matrices are the exact original FCP.BFSSGamma9.gamma construction,
not a substitute representation. Their accepted Clifford and symmetric
properties imply that each real-spinor-weighted kinetic row has spatial
Gram matrix ||w||² I. This is the finite-spinor input for recovering the
literal -1/2 Laplacian from the scalar part of the L6G4B normal-ordered
source charge square. The source kinetic coefficient itself retains -i;
its operator-level contraction is a separate subsequent obligation.

No H0, Gauss, spectral or physical-domain identity is asserted here.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G5A
noncomputable section
open scoped Matrix BigOperators
open OAI.BFSSGamma
open FCP.BFSSSU2PhysicalDomainL6G1
open FCP.BFSSSU2PhysicalDomainL6G2

/-- Real-spinor kinetic-row Gram identity for the literal source gamma.
This resolves the finite Clifford contraction for ALL real w, not just
unit spinors or the 16 coordinate-basis spinors. -/
theorem originalGamma_rowKineticGram (w : Spin → ℝ) (i j : Space) :
    dotProduct (w ᵥ* originalGamma i) (w ᵥ* originalGamma j) =
      if i = j then spinorSquareNorm w else 0 := by
  have hi : (originalGamma i).transpose = originalGamma i :=
    FCP.BFSSGamma9.gamma_symmetric i
  have hj : (originalGamma j).transpose = originalGamma j :=
    FCP.BFSSGamma9.gamma_symmetric j
  rw [originalGamma_row_eq_column w i, originalGamma_row_eq_column w j]
  rw [OAI.BFSSGamma.dot_mulVec_left, hi, Matrix.mulVec_mulVec]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl,
      OAI.BFSSGamma.gamma_sq originalGamma
        (fun a b => FCP.BFSSGamma9.gamma_clifford a b) i,
      Matrix.one_mulVec]
    change (∑ α : Spin, w α * w α) = ∑ α : Spin, w α ^ 2
    simp only [pow_two]
  · rw [if_neg hij]
    apply OAI.BFSSGamma.dot_skew_zero
    rw [Matrix.transpose_mul, hi, hj,
      OAI.BFSSGamma.gamma_anti originalGamma
        (fun a b => FCP.BFSSGamma9.gamma_clifford a b) (Ne.symm hij)]

#print axioms originalGamma_rowKineticGram
#check @originalGamma_rowKineticGram

end
end FCP.BFSSSU2PhysicalDomainL6G5A
