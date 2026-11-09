import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BFPBWCliffordTopologicalRing
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
F10BT — actual Clifford multiplication as a continuous bilinear map.

Candidate only until strict compilation and independent PBW/type/axiom
audit. Use the accepted named PBW norm and finite dimensionality to bundle
left multiplication, then its dependence on the left factor, continuously.
The existing bounded-bilinear calculus then proves every-order smoothness
of the actual ambient Clifford product.

No norm is changed and no NormedRing instance is registered. This supplies
ambient multiplication calculus, not a subgroup atlas, smooth inversion
on an open unit locus, source tangent identification or group differential.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open scoped ContDiff

local instance f10btLocalNormedAddCommGroup : NormedAddCommGroup (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedAddCommGroup

local instance f10btLocalNormedSpace : NormedSpace ℝ (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedSpace

local instance f10btLocalFiniteDimensional : FiniteDimensional ℝ (CliffordAlgebra source9Quadratic) :=
  source9Clifford_finiteDimensional

/-- Actual left multiplication, continuously bundled for the accepted PBW norm. -/
noncomputable def source9CliffordLeftMulCLM
    (a : CliffordAlgebra source9Quadratic) :
    CliffordAlgebra source9Quadratic →L[ℝ] CliffordAlgebra source9Quadratic :=
  { toLinearMap := Algebra.lmul ℝ (CliffordAlgebra source9Quadratic) a
    cont := (Algebra.lmul ℝ (CliffordAlgebra source9Quadratic) a).continuous_of_finiteDimensional }

/-- The actual product is continuously bilinear in the original accepted PBW vector space. -/
noncomputable def source9CliffordMulCLM :
    CliffordAlgebra source9Quadratic →L[ℝ]
      CliffordAlgebra source9Quadratic →L[ℝ] CliffordAlgebra source9Quadratic := by
  let L : CliffordAlgebra source9Quadratic →ₗ[ℝ]
      (CliffordAlgebra source9Quadratic →L[ℝ] CliffordAlgebra source9Quadratic) :=
    { toFun := source9CliffordLeftMulCLM
      map_add' := by
        intro a b
        apply ContinuousLinearMap.ext
        intro x
        change (a + b) * x = a * x + b * x
        exact add_mul a b x
      map_smul' := by
        intro c a
        apply ContinuousLinearMap.ext
        intro x
        change (c • a) * x = (RingHom.id ℝ) c • (a * x)
        rw [RingHom.id_apply, smul_mul_assoc] }
  exact { toLinearMap := L, cont := L.continuous_of_finiteDimensional }

/-- The bundled bilinear map evaluates to the existing Clifford multiplication, with no rescaling. -/
theorem source9CliffordMulCLM_apply
    (a b : CliffordAlgebra source9Quadratic) :
    source9CliffordMulCLM a b = a * b := rfl

/-- Actual ambient Clifford multiplication is C^n for every order under the accepted PBW norm. -/
theorem source9Clifford_mul_contDiff_pbw (n : ℕ∞ω) :
    ContDiff ℝ n
      (fun xy : CliffordAlgebra source9Quadratic × CliffordAlgebra source9Quadratic =>
        xy.1 * xy.2) := by
  change ContDiff ℝ n
    (fun xy : CliffordAlgebra source9Quadratic × CliffordAlgebra source9Quadratic =>
      source9CliffordMulCLM xy.1 xy.2)
  exact source9CliffordMulCLM.isBoundedBilinearMap.contDiff

#print axioms source9CliffordLeftMulCLM
#print axioms source9CliffordMulCLM
#print axioms source9CliffordMulCLM_apply
#print axioms source9Clifford_mul_contDiff_pbw

end
end FCP.BFSSPairedSpin9Clifford
