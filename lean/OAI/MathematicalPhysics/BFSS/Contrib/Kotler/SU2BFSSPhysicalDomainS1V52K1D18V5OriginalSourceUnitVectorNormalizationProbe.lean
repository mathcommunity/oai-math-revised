import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V4AOriginalSourcePositiveDefiniteStructuralProbe

/-!
K1D18V5 — unit-length normalization of nonzero vectors on the exact
original source `Fin 24 × Fin 2 → ℝ` and S1V0 `source48Quadratic`.
The abstract real-scalar denominator identity is proved separately;
the source theorem uses V4A's strictly accepted positivity, without
expanding an original 48-coordinate sum.

All declarations are CANDIDATES pending fresh source-pinned strict CI.
This does not establish original Clifford generator inverse/star,
Pin/Spin group membership, even Spin products, surjectivity, covering,
global Spin9 invariance or BFSS spectral existence.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V5
noncomputable section
open FCP.BFSSS1V0

/-- A strictly positive real number is normalized by the inverse
of its positive square root. Entirely scalar; no source-definitional
unfolding or 48-label calculation. -/
theorem real_sqrt_inv_square_mul_self
    (q : ℝ) (hq : 0 < q) :
    ((Real.sqrt q)⁻¹ * (Real.sqrt q)⁻¹) * q = 1 := by
  have hsqrt : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  calc
    ((Real.sqrt q)⁻¹ * (Real.sqrt q)⁻¹) * q =
        ((Real.sqrt q)⁻¹ * (Real.sqrt q)⁻¹) * (Real.sqrt q)^2 := by
      rw [Real.sq_sqrt hq.le]
    _ = 1 := by
      field_simp [hsqrt]

/-- Actual ORIGINAL quadratic normalization, without substituting
another quadratic form. All source labels and weights are unchanged.
The nonzero premise is discharged by accepted V4A positivity. -/
theorem source48Quadratic_normalized_value
    (a : Source48Vector) (ha : a ≠ 0) :
    source48Quadratic
      ((Real.sqrt (source48Quadratic a))⁻¹ • a) = 1 := by
  have hq : 0 < source48Quadratic a :=
    FCP.BFSSS1V52K1D18V4A.source48Quadratic_pos_of_ne_zero a ha
  calc
    source48Quadratic ((Real.sqrt (source48Quadratic a))⁻¹ • a) =
        ((Real.sqrt (source48Quadratic a))⁻¹ *
          (Real.sqrt (source48Quadratic a))⁻¹) * source48Quadratic a := by
      rw [QuadraticMap.map_smul]
      simp only [smul_eq_mul]
    _ = 1 := real_sqrt_inv_square_mul_self (source48Quadratic a) hq

/-- A nonzero original source vector explicitly produces a unit-Q
source vector with a named canonical witness. -/
theorem source48Quadratic_exists_unit_of_ne_zero
    (a : Source48Vector) (ha : a ≠ 0) :
    ∃ u : Source48Vector, source48Quadratic u = 1 := by
  exact ⟨(Real.sqrt (source48Quadratic a))⁻¹ • a,
    source48Quadratic_normalized_value a ha⟩

#print axioms real_sqrt_inv_square_mul_self
#print axioms source48Quadratic_normalized_value
#print axioms source48Quadratic_exists_unit_of_ne_zero

end
end FCP.BFSSS1V52K1D18V5
