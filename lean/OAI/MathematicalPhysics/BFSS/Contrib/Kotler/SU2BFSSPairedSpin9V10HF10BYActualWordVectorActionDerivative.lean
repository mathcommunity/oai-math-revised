import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BXWordDerivativeNativeVectorAction

/-!
F10BY — full finite-parameter derivative of actual source-word vector action.

Candidate only until strict compilation and independent PBW/type/axiom audit.
Use actual Clifford conjugation and the accepted inverse/reversal identity.
Differentiate with the accepted continuous bilinear product, then project
and use BX's exact full native-plane commutator transport.

The vector is fixed while all finite word parameters vary. This is an
ordinary derivative of an actual group-valued parameterization's vector
action. No source/target atlas, tangent Lie-algebra identification, native
model isomorphism or full group-map manifold differential is constructed.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSPairedSpin9Plane

local instance f10byLocalNormedAddCommGroup :
    NormedAddCommGroup (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedAddCommGroup
local instance f10byLocalNormedSpace :
    NormedSpace ℝ (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedSpace

/-- Grade reversal negates the exact source half-bivector for a distinct coordinate pair. -/
theorem source9CoordinateHalfBivector_reverse
    (r s : SpaceIndex) (hrs : r ≠ s) :
    CliffordAlgebra.reverse
      ((1 / 2 : ℝ) •
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s))) =
      -((1 / 2 : ℝ) •
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s))) := by
  simp only [map_smul, CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse_ι,
    source9CoordinateClifford_anticommute r s hrs, smul_neg]

/-- Reversal negates the full velocity of every actual distinct-plane word in every direction. -/
theorem source9PlaneSpinWordVelocity_reverse {k : ℕ}
    (r s : Fin k → SpaceIndex) (hrs : ∀ i, r i ≠ s i)
    (l : List (Fin k)) (v : Fin k → ℝ) :
    CliffordAlgebra.reverse (source9PlaneSpinWordVelocity r s l v) =
      -source9PlaneSpinWordVelocity r s l v := by
  induction l with
  | nil =>
      change CliffordAlgebra.reverse (0 : CliffordAlgebra source9Quadratic) = -0
      simp only [map_zero, neg_zero]
  | cons i l ih =>
      have hhead :
          CliffordAlgebra.reverse (source9PlaneParameterVelocity (r i) (s i) i v) =
            -source9PlaneParameterVelocity (r i) (s i) i v := by
        change CliffordAlgebra.reverse
          (v i • ((1 / 2 : ℝ) •
            (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (r i)) *
              CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (s i))))) =
          -(v i • ((1 / 2 : ℝ) •
            (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (r i)) *
              CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (s i)))))
        rw [map_smul, source9CoordinateHalfBivector_reverse (r i) (s i) (hrs i), smul_neg]
      change CliffordAlgebra.reverse
        (source9PlaneParameterVelocity (r i) (s i) i v +
          source9PlaneSpinWordVelocity r s l v) =
        -(source9PlaneParameterVelocity (r i) (s i) i v +
          source9PlaneSpinWordVelocity r s l v)
      rw [map_add, hhead, ih, neg_add]

/-- Actual source-word Clifford conjugation has the commutator derivative at zero. -/
theorem source9PlaneSpinWord_conjugation_hasFDerivAt_zero {k : ℕ}
    (r s : Fin k → SpaceIndex) (hrs : ∀ i, r i ≠ s i)
    (l : List (Fin k)) (z : SpaceIndex → ℝ) :
    HasFDerivAt
      (fun t : Fin k → ℝ =>
        ((source9PlaneSpinWord r s hrs t l) : CliffordAlgebra source9Quadratic) *
          CliffordAlgebra.ι source9Quadratic z *
          (((source9PlaneSpinWord r s hrs t l)⁻¹ : spinGroup source9Quadratic) :
            CliffordAlgebra source9Quadratic))
      ((source9CliffordMulCLM.flip (CliffordAlgebra.ι source9Quadratic z) -
        source9CliffordMulCLM (CliffordAlgebra.ι source9Quadratic z)).comp
          (source9PlaneSpinWordVelocity r s l)) 0 := by
  let W : (Fin k → ℝ) → CliffordAlgebra source9Quadratic :=
    fun t => ((source9PlaneSpinWord r s hrs t l) : CliffordAlgebra source9Quadratic)
  let H : (Fin k → ℝ) →L[ℝ] CliffordAlgebra source9Quadratic :=
    source9PlaneSpinWordVelocity r s l
  let L : CliffordAlgebra source9Quadratic →L[ℝ] CliffordAlgebra source9Quadratic :=
    source9CliffordMulCLM.flip (CliffordAlgebra.ι source9Quadratic z)
  have hW : HasFDerivAt W H (0 : Fin k → ℝ) :=
    source9PlaneSpinWord_coe_hasFDerivAt_zero r s hrs l
  have hleft : HasFDerivAt (fun t => L (W t)) (L.comp H) (0 : Fin k → ℝ) :=
    L.hasFDerivAt.comp (0 : Fin k → ℝ) hW
  have hreverse : HasFDerivAt (fun t => source9CliffordReverseCLM (W t))
      (source9CliffordReverseCLM.comp H) (0 : Fin k → ℝ) :=
    source9CliffordReverseCLM.hasFDerivAt.comp (0 : Fin k → ℝ) hW
  have hproduct := source9CliffordMulCLM.hasFDerivAt_of_bilinear hleft hreverse
  have hzero : W 0 = 1 :=
    congrArg (fun g : spinGroup source9Quadratic =>
      (g : CliffordAlgebra source9Quadratic)) (source9PlaneSpinWord_zero r s hrs l)
  have hlinear :
      source9CliffordMulCLM.precompR (Fin k → ℝ) (L (W 0))
        (source9CliffordReverseCLM.comp H) +
      source9CliffordMulCLM.precompL (Fin k → ℝ) (L.comp H)
        (source9CliffordReverseCLM (W 0)) =
      (L - source9CliffordMulCLM (CliffordAlgebra.ι source9Quadratic z)).comp H := by
    apply ContinuousLinearMap.ext
    intro v
    change
      (W 0 * CliffordAlgebra.ι source9Quadratic z) *
          CliffordAlgebra.reverse (source9PlaneSpinWordVelocity r s l v) +
        (source9PlaneSpinWordVelocity r s l v * CliffordAlgebra.ι source9Quadratic z) *
          CliffordAlgebra.reverse (W 0) =
      source9PlaneSpinWordVelocity r s l v * CliffordAlgebra.ι source9Quadratic z -
        CliffordAlgebra.ι source9Quadratic z * source9PlaneSpinWordVelocity r s l v
    simp only [hzero, one_mul, CliffordAlgebra.reverse.map_one, mul_one,
      source9PlaneSpinWordVelocity_reverse r s hrs l v, mul_neg, sub_eq_add_neg]
    exact add_comm _ _
  have heq :
      (fun t : Fin k → ℝ =>
        source9CliffordMulCLM (L (W t)) (source9CliffordReverseCLM (W t))) =
      (fun t : Fin k → ℝ =>
        ((source9PlaneSpinWord r s hrs t l) : CliffordAlgebra source9Quadratic) *
          CliffordAlgebra.ι source9Quadratic z *
          (((source9PlaneSpinWord r s hrs t l)⁻¹ : spinGroup source9Quadratic) :
            CliffordAlgebra source9Quadratic)) := by
    funext t
    change (W t * CliffordAlgebra.ι source9Quadratic z) * CliffordAlgebra.reverse (W t) =
      (W t * CliffordAlgebra.ι source9Quadratic z) *
        (((source9PlaneSpinWord r s hrs t l)⁻¹ : spinGroup source9Quadratic) :
          CliffordAlgebra source9Quadratic)
    rw [source9Spin_inv_coe_eq_reverse]
  rw [hlinear, heq] at hproduct
  exact hproduct

/-- Full finite-parameter derivative of the actual nine-vector action, at the zero parameter. -/
theorem source9PlaneSpinWord_vectorAction_hasFDerivAt_zero {k : ℕ}
    (r s : Fin k → SpaceIndex) (hrs : ∀ i, r i ≠ s i)
    (l : List (Fin k)) (z : SpaceIndex → ℝ) :
    HasFDerivAt
      (fun t : Fin k → ℝ => source9SpinVectorConjugation (source9PlaneSpinWord r s hrs t l) z)
      (source9PlaneWordVectorVelocity r s z l) 0 := by
  have h := source9VectorProjectionCLM.hasFDerivAt.comp (0 : Fin k → ℝ)
    (source9PlaneSpinWord_conjugation_hasFDerivAt_zero r s hrs l z)
  have hlinear :
      source9VectorProjectionCLM.comp
        ((source9CliffordMulCLM.flip (CliffordAlgebra.ι source9Quadratic z) -
          source9CliffordMulCLM (CliffordAlgebra.ι source9Quadratic z)).comp
            (source9PlaneSpinWordVelocity r s l)) =
      source9PlaneWordVectorVelocity r s z l := by
    apply ContinuousLinearMap.ext
    intro v
    change source9CliffordVectorProjection
      (source9PlaneSpinWordVelocity r s l v * CliffordAlgebra.ι source9Quadratic z -
        CliffordAlgebra.ι source9Quadratic z * source9PlaneSpinWordVelocity r s l v) =
      source9PlaneWordVectorVelocity r s z l v
    exact source9PlaneSpinWordVelocity_projected_commutator r s l v z
  have heq :
      source9VectorProjectionCLM ∘
        (fun t : Fin k → ℝ =>
          ((source9PlaneSpinWord r s hrs t l) : CliffordAlgebra source9Quadratic) *
            CliffordAlgebra.ι source9Quadratic z *
            (((source9PlaneSpinWord r s hrs t l)⁻¹ : spinGroup source9Quadratic) :
              CliffordAlgebra source9Quadratic)) =
      (fun t : Fin k → ℝ =>
        source9SpinVectorConjugation (source9PlaneSpinWord r s hrs t l) z) := by
    funext t
    rfl
  rw [hlinear, heq] at h
  exact h

/-- Actual vector-action fderiv is exactly the qualified full native-plane linear map. -/
theorem source9PlaneSpinWord_vectorAction_fderiv_zero {k : ℕ}
    (r s : Fin k → SpaceIndex) (hrs : ∀ i, r i ≠ s i)
    (l : List (Fin k)) (z : SpaceIndex → ℝ) :
    fderiv ℝ
      (fun t : Fin k → ℝ => source9SpinVectorConjugation (source9PlaneSpinWord r s hrs t l) z) 0 =
      source9PlaneWordVectorVelocity r s z l :=
  (source9PlaneSpinWord_vectorAction_hasFDerivAt_zero r s hrs l z).fderiv

/-- In every direction the actual action derivative is the literal sum of full native planes. -/
theorem source9PlaneSpinWord_vectorAction_fderiv_zero_apply {k : ℕ}
    (r s : Fin k → SpaceIndex) (hrs : ∀ i, r i ≠ s i)
    (l : List (Fin k)) (z : SpaceIndex → ℝ) (v : Fin k → ℝ) :
    (fderiv ℝ
      (fun t : Fin k → ℝ => source9SpinVectorConjugation (source9PlaneSpinWord r s hrs t l) z) 0) v =
      (l.map (fun i => v i • ((coordinatePlane9 (r i) (s i)).mulVec z))).sum := by
  have hmap :
      fderiv ℝ
        (fun t : Fin k → ℝ =>
          source9SpinVectorConjugation (source9PlaneSpinWord r s hrs t l) z) 0 =
      source9PlaneWordVectorVelocity r s z l :=
    source9PlaneSpinWord_vectorAction_fderiv_zero r s hrs l z
  exact (congrArg (fun L : (Fin k → ℝ) →L[ℝ] (SpaceIndex → ℝ) =>
    L v) hmap).trans (source9PlaneWordVectorVelocity_apply r s z l v)

#print axioms source9CoordinateHalfBivector_reverse
#print axioms source9PlaneSpinWordVelocity_reverse
#print axioms source9PlaneSpinWord_conjugation_hasFDerivAt_zero
#print axioms source9PlaneSpinWord_vectorAction_hasFDerivAt_zero
#print axioms source9PlaneSpinWord_vectorAction_fderiv_zero
#print axioms source9PlaneSpinWord_vectorAction_fderiv_zero_apply

end
end FCP.BFSSPairedSpin9Clifford
