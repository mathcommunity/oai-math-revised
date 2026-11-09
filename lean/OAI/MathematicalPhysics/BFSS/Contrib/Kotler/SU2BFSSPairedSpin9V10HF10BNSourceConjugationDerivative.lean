import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BMInverseSourceCurveDerivative

/-!
F10BN — derivative of actual source plane-curve conjugation.

Candidate only until fresh strict compilation and independent PBW/type/axiom
audit. Expand the accepted source curve and its actual inverse into four
scalar-coefficient terms. Only scalar products are differentiated; Clifford
multiplication occurs between fixed coefficients. No normed-ring instance
or unproved multiplication estimate is needed.

The final derivative acts on every actual source nine-vector by the literal
native coordinate plane. This is an ambient PBW-vector-space derivative,
not a manifold tangent identification or a global group-map differential.
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

/-- Four fixed vector coefficients with half-angle scalar products have the stated velocity. -/
theorem realHalfAngleQuadraticVectorCurve_hasDerivAt_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (a b c d : V) :
    HasDerivAt (fun t : ℝ =>
      ((Real.cos (t / 2) * Real.cos (t / 2)) • a +
        (Real.cos (t / 2) * Real.sin (t / 2)) • b) +
      ((Real.sin (t / 2) * Real.cos (t / 2)) • c +
        (Real.sin (t / 2) * Real.sin (t / 2)) • d))
      ((1 / 2 : ℝ) • b + (1 / 2 : ℝ) • c) 0 := by
  have hc : HasDerivAt (fun t : ℝ => Real.cos (t / 2)) 0 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).div_const 2).cos)
  have hs : HasDerivAt (fun t : ℝ => Real.sin (t / 2)) (1 / 2 : ℝ) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).div_const 2).sin)
  have hproduct {f g : ℝ → ℝ} {f' g' : ℝ}
      (hf : HasDerivAt f f' 0) (hg : HasDerivAt g g' 0) :
      HasDerivAt (fun t : ℝ => f t * g t) (f' * g 0 + f 0 * g') 0 := by
    have heq : f * g = (fun t : ℝ => f t * g t) := by
      funext t
      rfl
    have h := hf.mul hg
    rw [heq] at h
    exact h
  have hcc : HasDerivAt
      (fun t : ℝ => Real.cos (t / 2) * Real.cos (t / 2)) 0 0 := by
    simpa using (hproduct hc hc)
  have hcs : HasDerivAt
      (fun t : ℝ => Real.cos (t / 2) * Real.sin (t / 2)) (1 / 2 : ℝ) 0 := by
    simpa using (hproduct hc hs)
  have hsc : HasDerivAt
      (fun t : ℝ => Real.sin (t / 2) * Real.cos (t / 2)) (1 / 2 : ℝ) 0 := by
    simpa using (hproduct hs hc)
  have hss : HasDerivAt
      (fun t : ℝ => Real.sin (t / 2) * Real.sin (t / 2)) 0 0 := by
    simpa using (hproduct hs hs)
  have hadd :
      (((fun t : ℝ => (Real.cos (t / 2) * Real.cos (t / 2)) • a) +
        (fun t : ℝ => (Real.cos (t / 2) * Real.sin (t / 2)) • b)) +
      ((fun t : ℝ => (Real.sin (t / 2) * Real.cos (t / 2)) • c) +
        (fun t : ℝ => (Real.sin (t / 2) * Real.sin (t / 2)) • d))) =
      (fun t : ℝ =>
        ((Real.cos (t / 2) * Real.cos (t / 2)) • a +
          (Real.cos (t / 2) * Real.sin (t / 2)) • b) +
        ((Real.sin (t / 2) * Real.cos (t / 2)) • c +
          (Real.sin (t / 2) * Real.sin (t / 2)) • d)) := by
    funext t
    rfl
  have hsum := ((hcc.smul_const a).add (hcs.smul_const b)).add
    ((hsc.smul_const c).add (hss.smul_const d))
  rw [hadd] at hsum
  simpa only [zero_smul, zero_add, add_zero] using hsum

/-- Exact scalar expansion of conjugation by the actual source curve and group inverse. -/
theorem source9PlaneSpinCurve_conjugation_coe
    (r s : SpaceIndex) (hrs : r ≠ s)
    (W : CliffordAlgebra source9Quadratic) (t : ℝ) :
    ((source9PlaneSpinCurve r s hrs t) : CliffordAlgebra source9Quadratic) * W *
      (((source9PlaneSpinCurve r s hrs t)⁻¹ : spinGroup source9Quadratic) :
        CliffordAlgebra source9Quadratic) =
      ((Real.cos (t / 2) * Real.cos (t / 2)) • W +
        (Real.cos (t / 2) * Real.sin (t / 2)) • (W * (-(CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s))))) +
      ((Real.sin (t / 2) * Real.cos (t / 2)) • ((CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s)) * W) +
        (Real.sin (t / 2) * Real.sin (t / 2)) •
          (((CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s)) * W) * (-(CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s))))) := by
  let B : CliffordAlgebra source9Quadratic := (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s))
  let c : ℝ := Real.cos (t / 2)
  let d : ℝ := Real.sin (t / 2)
  have hmul (a b : ℝ) (x y : CliffordAlgebra source9Quadratic) :
      (a • x) * (b • y) = (a * b) • (x * y) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [source9PlaneSpinCurve_coe, source9PlaneSpinCurve_inv_coe]
  change ((c • (1 : CliffordAlgebra source9Quadratic) + d • B) * W) *
      (c • (1 : CliffordAlgebra source9Quadratic) + d • (-B)) =
    ((c * c) • W + (c * d) • (W * (-B))) +
      ((d * c) • (B * W) + (d * d) • ((B * W) * (-B)))
  have hleft :
      (c • (1 : CliffordAlgebra source9Quadratic) + d • B) * W =
        c • W + d • (B * W) := by
    rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc]
  rw [hleft, add_mul, mul_add, mul_add]
  simp only [hmul, mul_one]

/-- Ambient PBW derivative of actual source conjugation on an arbitrary Clifford element. -/
theorem source9PlaneSpinCurve_conjugation_hasDerivAt_zero
    (r s : SpaceIndex) (hrs : r ≠ s) (W : CliffordAlgebra source9Quadratic) :
    HasDerivAt (fun t : ℝ =>
      ((source9PlaneSpinCurve r s hrs t) : CliffordAlgebra source9Quadratic) * W *
        (((source9PlaneSpinCurve r s hrs t)⁻¹ : spinGroup source9Quadratic) :
          CliffordAlgebra source9Quadratic))
      ((((1 / 2 : ℝ) • (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s))) * W) -
        W * ((1 / 2 : ℝ) • (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s)))) 0 := by
  let B : CliffordAlgebra source9Quadratic := (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s))
  have heq :
      (fun t : ℝ =>
        ((source9PlaneSpinCurve r s hrs t) : CliffordAlgebra source9Quadratic) * W *
          (((source9PlaneSpinCurve r s hrs t)⁻¹ : spinGroup source9Quadratic) :
            CliffordAlgebra source9Quadratic)) =
      (fun t : ℝ =>
        ((Real.cos (t / 2) * Real.cos (t / 2)) • W +
          (Real.cos (t / 2) * Real.sin (t / 2)) • (W * (-B))) +
        ((Real.sin (t / 2) * Real.cos (t / 2)) • (B * W) +
          (Real.sin (t / 2) * Real.sin (t / 2)) • ((B * W) * (-B)))) := by
    funext t
    exact source9PlaneSpinCurve_conjugation_coe r s hrs W t
  rw [heq]
  have hvelocity :
      (1 / 2 : ℝ) • (W * (-B)) + (1 / 2 : ℝ) • (B * W) =
        ((1 / 2 : ℝ) • B) * W - W * ((1 / 2 : ℝ) • B) := by
    rw [smul_mul_assoc, mul_smul_comm, mul_neg, smul_neg]
    abel
  have hderiv := realHalfAngleQuadraticVectorCurve_hasDerivAt_zero
    W (W * (-B)) (B * W) ((B * W) * (-B))
  rw [hvelocity] at hderiv
  exact hderiv

/-- On every actual source vector, the conjugation derivative is the unchanged native plane action. -/
theorem source9PlaneSpinCurve_conjugation_vector_hasDerivAt_zero
    (r s : SpaceIndex) (hrs : r ≠ s) (z : SpaceIndex → ℝ) :
    HasDerivAt (fun t : ℝ =>
      ((source9PlaneSpinCurve r s hrs t) : CliffordAlgebra source9Quadratic) *
        CliffordAlgebra.ι source9Quadratic z *
        (((source9PlaneSpinCurve r s hrs t)⁻¹ : spinGroup source9Quadratic) :
          CliffordAlgebra source9Quadratic))
      (CliffordAlgebra.ι source9Quadratic ((coordinatePlane9 r s).mulVec z)) 0 := by
  have hderiv := source9PlaneSpinCurve_conjugation_hasDerivAt_zero r s hrs
    (CliffordAlgebra.ι source9Quadratic z)
  rw [source9CoordinateBivector_commutator_vector] at hderiv
  exact hderiv

#print axioms realHalfAngleQuadraticVectorCurve_hasDerivAt_zero
#print axioms source9PlaneSpinCurve_conjugation_coe
#print axioms source9PlaneSpinCurve_conjugation_hasDerivAt_zero
#print axioms source9PlaneSpinCurve_conjugation_vector_hasDerivAt_zero

end
end FCP.BFSSPairedSpin9Clifford
