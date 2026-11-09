import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BNSourceConjugationDerivative
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
F10BO — actual source-vector conjugation and its plane-curve derivative.

Candidate only until strict compilation and independent PBW/type/axiom
audit. Use the existing real-linear Clifford/exterior equivalence and
ExteriorAlgebra.ιInv to recover source vectors. Spin conjugation is in
the embedded vector range by the pinned Mathlib theorem.

The output is the original nine-vector space with its standard Pi norm.
The final theorem differentiates this actual vector-valued conjugation,
not just its Clifford embedding. No source manifold tangent space or
global F10BC differential is identified.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSPairedSpin9Plane

local instance : NormedAddCommGroup (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedAddCommGroup

local instance : NormedSpace ℝ (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedSpace

local instance : FiniteDimensional ℝ (CliffordAlgebra source9Quadratic) :=
  source9Clifford_finiteDimensional

/-- Canonical real-linear vector recovery through the accepted Clifford/exterior equivalence. -/
noncomputable def source9CliffordVectorProjection :
    CliffordAlgebra source9Quadratic →ₗ[ℝ] (SpaceIndex → ℝ) :=
  (ExteriorAlgebra.ιInv :
    ExteriorAlgebra ℝ (SpaceIndex → ℝ) →ₗ[ℝ] (SpaceIndex → ℝ)).comp
      (CliffordAlgebra.equivExterior source9Quadratic).toLinearMap

/-- Vector recovery is a left inverse of the actual source Clifford embedding. -/
theorem source9CliffordVectorProjection_ι (z : SpaceIndex → ℝ) :
    source9CliffordVectorProjection (CliffordAlgebra.ι source9Quadratic z) = z := by
  change ExteriorAlgebra.ιInv
    ((CliffordAlgebra.equivExterior source9Quadratic)
      (CliffordAlgebra.ι source9Quadratic z)) = z
  have heq :
      (CliffordAlgebra.equivExterior source9Quadratic)
        (CliffordAlgebra.ι source9Quadratic z) = ExteriorAlgebra.ι ℝ z :=
    CliffordAlgebra.changeForm_ι
      (CliffordAlgebra.changeForm.associated_neg_proof (Q := source9Quadratic)) z
  rw [heq]
  exact ExteriorAlgebra.ι_leftInverse (R := ℝ) z

/-- The canonical vector projection is continuous for the accepted PBW norm and standard Pi norm. -/
theorem source9CliffordVectorProjection_continuous_pbw :
    Continuous source9CliffordVectorProjection := by
  exact source9CliffordVectorProjection.continuous_of_finiteDimensional

/-- Every actual source Spin element conjugates embedded nine-vectors into the same vector range. -/
theorem source9Spin_conjugation_mem_range
    (g : spinGroup source9Quadratic) (z : SpaceIndex → ℝ) :
    (g : CliffordAlgebra source9Quadratic) * CliffordAlgebra.ι source9Quadratic z *
      ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic) ∈
        LinearMap.range (CliffordAlgebra.ι source9Quadratic) := by
  have hmem :
      ((spinGroup.toUnits g : (CliffordAlgebra source9Quadratic)ˣ) :
        CliffordAlgebra source9Quadratic) ∈ spinGroup source9Quadratic := g.property
  have h := spinGroup.conjAct_smul_ι_mem_range_ι
    (Q := source9Quadratic) (x := spinGroup.toUnits g) hmem z
  rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct] at h
  change (g : CliffordAlgebra source9Quadratic) * CliffordAlgebra.ι source9Quadratic z *
    ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic) ∈
      LinearMap.range (CliffordAlgebra.ι source9Quadratic) at h
  exact h

/-- Actual source-vector conjugation, recovered canonically from its Clifford expression. -/
noncomputable def source9SpinVectorConjugation
    (g : spinGroup source9Quadratic) (z : SpaceIndex → ℝ) : SpaceIndex → ℝ :=
  source9CliffordVectorProjection
    ((g : CliffordAlgebra source9Quadratic) * CliffordAlgebra.ι source9Quadratic z *
      ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic))

/-- The recovered vector embeds back to the exact actual-group conjugation expression. -/
theorem source9SpinVectorConjugation_ι
    (g : spinGroup source9Quadratic) (z : SpaceIndex → ℝ) :
    CliffordAlgebra.ι source9Quadratic (source9SpinVectorConjugation g z) =
      (g : CliffordAlgebra source9Quadratic) * CliffordAlgebra.ι source9Quadratic z *
        ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic) := by
  obtain ⟨w, hw⟩ := source9Spin_conjugation_mem_range g z
  change CliffordAlgebra.ι source9Quadratic
      (source9CliffordVectorProjection
        ((g : CliffordAlgebra source9Quadratic) * CliffordAlgebra.ι source9Quadratic z *
          ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic))) = _
  calc
    _ = CliffordAlgebra.ι source9Quadratic
        (source9CliffordVectorProjection (CliffordAlgebra.ι source9Quadratic w)) := by
      rw [hw]
    _ = CliffordAlgebra.ι source9Quadratic w := by
      rw [source9CliffordVectorProjection_ι]
    _ = _ := hw

/-- On the original nine-vector space, the actual conjugation curve has literal native-plane velocity. -/
theorem source9PlaneSpinCurve_vectorConjugation_hasDerivAt_zero
    (r s : SpaceIndex) (hrs : r ≠ s) (z : SpaceIndex → ℝ) :
    HasDerivAt (fun t : ℝ => source9SpinVectorConjugation
      (source9PlaneSpinCurve r s hrs t) z) ((coordinatePlane9 r s).mulVec z) 0 := by
  let P : CliffordAlgebra source9Quadratic →L[ℝ] (SpaceIndex → ℝ) :=
    { toLinearMap := source9CliffordVectorProjection
      cont := source9CliffordVectorProjection_continuous_pbw }
  have h := P.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (source9PlaneSpinCurve_conjugation_vector_hasDerivAt_zero r s hrs z)
  have heq :
      P ∘ (fun t : ℝ =>
        ((source9PlaneSpinCurve r s hrs t) : CliffordAlgebra source9Quadratic) *
          CliffordAlgebra.ι source9Quadratic z *
          (((source9PlaneSpinCurve r s hrs t)⁻¹ : spinGroup source9Quadratic) :
            CliffordAlgebra source9Quadratic)) =
      (fun t : ℝ => source9SpinVectorConjugation (source9PlaneSpinCurve r s hrs t) z) := by
    funext t
    rfl
  rw [heq] at h
  have hvalue :
      P (CliffordAlgebra.ι source9Quadratic ((coordinatePlane9 r s).mulVec z)) =
        (coordinatePlane9 r s).mulVec z :=
    source9CliffordVectorProjection_ι ((coordinatePlane9 r s).mulVec z)
  rw [hvalue] at h
  exact h

#print axioms source9CliffordVectorProjection
#print axioms source9CliffordVectorProjection_ι
#print axioms source9CliffordVectorProjection_continuous_pbw
#print axioms source9Spin_conjugation_mem_range
#print axioms source9SpinVectorConjugation
#print axioms source9SpinVectorConjugation_ι
#print axioms source9PlaneSpinCurve_vectorConjugation_hasDerivAt_zero

end
end FCP.BFSSPairedSpin9Clifford
