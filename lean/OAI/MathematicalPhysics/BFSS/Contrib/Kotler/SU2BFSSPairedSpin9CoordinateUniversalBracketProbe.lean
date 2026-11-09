import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9CoordinatePlaneProductExpansionProbe

/-!
K1D18V8W — native nine-index input so(9) generator commutator.

The source-native F_rs := E_rs-E_sr product is accepted V8V. Prove
a typed conditional bridge to Matrix.single and use its four-term
product on each side of [F_rs,F_tu], grouping terms by additive
matrix arithmetic. All index coincidences are admitted.

This is a generator bracket, not a linear homomorphism on arbitrary
skew 9×9 matrices, nor a Spin(9) lift or a BFSS result.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum

/-- Explicit universal standard so(9) coordinate-plane bracket RHS. -/
noncomputable def coordinateFourIndexRHS (r s t u : SpaceIndex) :
    Matrix SpaceIndex SpaceIndex ℝ :=
  -(if s = u then coordinatePlane9 r t else 0) +
  (if s = t then coordinatePlane9 r u else 0) -
  (if r = t then coordinatePlane9 s u else 0) +
  (if r = u then coordinatePlane9 s t else 0)

/-- A conditional native coordinate plane equals the corresponding
conditional subtraction of Mathlib's nine-index matrix units. -/
theorem coordinatePlane9_conditional_single_sub_single
    (p : Prop) [Decidable p] (r s : SpaceIndex) :
    (if p then coordinatePlane9 r s else 0) =
    (if p then (Matrix.single r s (1 : ℝ) :
        Matrix SpaceIndex SpaceIndex ℝ) else 0) -
    (if p then (Matrix.single s r (1 : ℝ) :
        Matrix SpaceIndex SpaceIndex ℝ) else 0) := by
  by_cases hp : p
  · simp only [hp, ite_true]
    exact coordinatePlane9_eq_single_sub_single r s
  · simp [hp]

/-- Universal source-native 9×9 so(9) coordinate-generator bracket,
including every spatial-label coincidence and with the same
structure constants as the accepted V8R 48-real H generators. -/
theorem coordinatePlane9_universal_four_index_bracket
    (r s t u : SpaceIndex) :
    coordinatePlane9 r s * coordinatePlane9 t u -
      coordinatePlane9 t u * coordinatePlane9 r s =
    coordinateFourIndexRHS r s t u := by
  rw [coordinatePlane9_mul_expanded r s t u,
      coordinatePlane9_mul_expanded t u r s]
  unfold coordinateFourIndexRHS
  rw [coordinatePlane9_conditional_single_sub_single (s = u) r t,
      coordinatePlane9_conditional_single_sub_single (s = t) r u,
      coordinatePlane9_conditional_single_sub_single (r = t) s u,
      coordinatePlane9_conditional_single_sub_single (r = u) s t]
  simp only [eq_comm]
  abel

#print axioms coordinatePlane9_conditional_single_sub_single
#print axioms coordinatePlane9_universal_four_index_bracket

end
end FCP.BFSSPairedSpin9Plane
