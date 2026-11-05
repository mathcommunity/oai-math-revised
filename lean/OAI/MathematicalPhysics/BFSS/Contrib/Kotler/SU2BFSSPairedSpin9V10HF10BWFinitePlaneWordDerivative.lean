import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BVFinitePlaneWordSmoothness
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
F10BW — full ambient derivative at zero of finite ordered actual source words.

Candidate only until fresh strict compilation and independent PBW/type/axiom
audit. Reuse the accepted actual one-plane velocity and actual continuous
bilinear Clifford multiplication. The finite parameter derivative is the sum
of coordinate-evaluation maps times the exact positive half-bivectors.

This is a derivative of the underlying Clifford-valued parameterization.
It is not a source tangent-space identification, a native skew-space
isomorphism, the derivative of the vector action, a chart or a group-map
manifold differential.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum

local instance f10bwLocalNormedAddCommGroup :
    NormedAddCommGroup (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedAddCommGroup
local instance f10bwLocalNormedSpace :
    NormedSpace ℝ (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedSpace

/-- The exact half-bivector velocity applied to one finite real coordinate. -/
noncomputable def source9PlaneParameterVelocity {k : ℕ}
    (r s : SpaceIndex) (i : Fin k) :
    (Fin k → ℝ) →L[ℝ] CliffordAlgebra source9Quadratic :=
  (ContinuousLinearMap.toSpanSingleton ℝ
    ((1 / 2 : ℝ) •
      (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
        CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s)))).comp
    (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)

/-- Actual one-plane curve, precomposed with one coordinate, has the exact finite derivative. -/
theorem source9PlaneParameterCurve_hasFDerivAt_zero {k : ℕ}
    (r s : SpaceIndex) (hrs : r ≠ s) (i : Fin k) :
    HasFDerivAt
      (fun t : Fin k → ℝ =>
        ((source9PlaneSpinCurve r s hrs (t i)) : CliffordAlgebra source9Quadratic))
      (source9PlaneParameterVelocity r s i) 0 := by
  let P : (Fin k → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hP : HasFDerivAt (fun t : Fin k → ℝ => t i) P (0 : Fin k → ℝ) :=
    P.hasFDerivAt
  exact (source9PlaneSpinCurve_coe_hasDerivAt_zero r s hrs).hasFDerivAt.comp
    (0 : Fin k → ℝ) hP

/-- The full linear candidate derivative sums the listed coordinate half-bivector maps. -/
noncomputable def source9PlaneSpinWordVelocity {k : ℕ}
    (r s : Fin k → SpaceIndex) :
    List (Fin k) → ((Fin k → ℝ) →L[ℝ] CliffordAlgebra source9Quadratic)
  | [] => 0
  | i :: l => source9PlaneParameterVelocity (r i) (s i) i +
      source9PlaneSpinWordVelocity r s l

/-- The derivative's value is the literal finite sum, retaining repetitions and the half factor. -/
theorem source9PlaneSpinWordVelocity_apply {k : ℕ}
    (r s : Fin k → SpaceIndex) (l : List (Fin k)) (v : Fin k → ℝ) :
    source9PlaneSpinWordVelocity r s l v =
      (l.map (fun i => v i • ((1 / 2 : ℝ) •
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (r i)) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (s i)))))).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      simp only [source9PlaneSpinWordVelocity, add_apply,
        List.map_cons, List.sum_cons]
      change v i • ((1 / 2 : ℝ) •
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (r i)) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (s i)))) +
          source9PlaneSpinWordVelocity r s l v =
        v i • ((1 / 2 : ℝ) •
          (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (r i)) *
            CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (s i)))) +
          (l.map (fun j => v j • ((1 / 2 : ℝ) •
            (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (r j)) *
              CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (s j)))))).sum
      rw [ih]

/-- Full ambient Fréchet derivative of the actual ordered word at the all-zero parameter. -/
theorem source9PlaneSpinWord_coe_hasFDerivAt_zero {k : ℕ}
    (r s : Fin k → SpaceIndex) (hrs : ∀ i, r i ≠ s i) (l : List (Fin k)) :
    HasFDerivAt (fun t : Fin k → ℝ =>
      ((source9PlaneSpinWord r s hrs t l) : CliffordAlgebra source9Quadratic))
      (source9PlaneSpinWordVelocity r s l) 0 := by
  induction l with
  | nil => exact hasFDerivAt_const (1 : CliffordAlgebra source9Quadratic) (0 : Fin k → ℝ)
  | cons i l ih =>
      have h := source9CliffordMulCLM.hasFDerivAt_of_bilinear
        (source9PlaneParameterCurve_hasFDerivAt_zero (r i) (s i) (hrs i) i) ih
      have hc0 :
          ((source9PlaneSpinCurve (r i) (s i) (hrs i) ((0 : Fin k → ℝ) i)) :
            CliffordAlgebra source9Quadratic) = 1 := by
        change ((source9PlaneSpinCurve (r i) (s i) (hrs i) 0) :
          CliffordAlgebra source9Quadratic) = 1
        exact congrArg (fun g : spinGroup source9Quadratic =>
          (g : CliffordAlgebra source9Quadratic)) (source9PlaneSpinCurve_zero (r i) (s i) (hrs i))
      have hw0 :
          ((source9PlaneSpinWord r s hrs 0 l) : CliffordAlgebra source9Quadratic) = 1 :=
        congrArg (fun g : spinGroup source9Quadratic =>
          (g : CliffordAlgebra source9Quadratic)) (source9PlaneSpinWord_zero r s hrs l)
      have hlinear :
          source9CliffordMulCLM.precompR (Fin k → ℝ)
            (((source9PlaneSpinCurve (r i) (s i) (hrs i) ((0 : Fin k → ℝ) i)) :
              CliffordAlgebra source9Quadratic)) (source9PlaneSpinWordVelocity r s l) +
          source9CliffordMulCLM.precompL (Fin k → ℝ)
            (source9PlaneParameterVelocity (r i) (s i) i)
            (((source9PlaneSpinWord r s hrs 0 l) : CliffordAlgebra source9Quadratic)) =
          source9PlaneSpinWordVelocity r s (i :: l) := by
        apply ContinuousLinearMap.ext
        intro v
        change
          (((source9PlaneSpinCurve (r i) (s i) (hrs i) ((0 : Fin k → ℝ) i)) :
            CliffordAlgebra source9Quadratic)) * source9PlaneSpinWordVelocity r s l v +
            source9PlaneParameterVelocity (r i) (s i) i v *
              (((source9PlaneSpinWord r s hrs 0 l) : CliffordAlgebra source9Quadratic)) =
          source9PlaneParameterVelocity (r i) (s i) i v +
            source9PlaneSpinWordVelocity r s l v
        rw [hc0, hw0, one_mul, mul_one]
        exact add_comm _ _
      rw [hlinear] at h
      exact h

/-- The actual ambient fderiv at zero equals the independently evaluable finite linear sum. -/
theorem source9PlaneSpinWord_coe_fderiv_zero {k : ℕ}
    (r s : Fin k → SpaceIndex) (hrs : ∀ i, r i ≠ s i) (l : List (Fin k)) :
    fderiv ℝ (fun t : Fin k → ℝ =>
      ((source9PlaneSpinWord r s hrs t l) : CliffordAlgebra source9Quadratic)) 0 =
      source9PlaneSpinWordVelocity r s l :=
  (source9PlaneSpinWord_coe_hasFDerivAt_zero r s hrs l).fderiv

#print axioms source9PlaneParameterVelocity
#print axioms source9PlaneParameterCurve_hasFDerivAt_zero
#print axioms source9PlaneSpinWordVelocity
#print axioms source9PlaneSpinWordVelocity_apply
#print axioms source9PlaneSpinWord_coe_hasFDerivAt_zero
#print axioms source9PlaneSpinWord_coe_fderiv_zero

end
end FCP.BFSSPairedSpin9Clifford
