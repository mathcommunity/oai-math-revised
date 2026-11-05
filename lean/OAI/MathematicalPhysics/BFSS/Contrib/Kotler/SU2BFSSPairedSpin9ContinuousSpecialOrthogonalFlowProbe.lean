import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9SpecialOrthogonalExponentialProbe

/-!
K1D18V10B — source-exact original paired-Fock continuous real
one-parameter homomorphisms into genuine SO(48), not just O(48).

The strict V10A determinant-one theorem supplies actual
Matrix.specialOrthogonalGroup membership. The accepted V9W
composition/zero and V9Y real-parameter continuity proofs
supply the laws. All labels remain the original Source48Label.

Every homomorphism here has source Multiplicative ℝ (a fixed
one-parameter subgroup). This is NOT a group homomorphism
Spin(9) → SO(48), nor a Spin(48) covering, a global Spin9
lift or a BFSS physical/spectral theorem.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open NormedSpace

/-- The exact original real 48-label skew exponential defines
a genuine one-parameter monoid hom into special orthogonal matrices. -/
noncomputable def pairedSkewOneParameterSpecialOrthogonalHom
    (X : Matrix Source48Label Source48Label ℝ)
    (hX : X.transpose = -X) :
    Multiplicative ℝ →*
      Matrix.specialOrthogonalGroup Source48Label ℝ where
  toFun := fun u =>
    ⟨exp ((Multiplicative.toAdd u) • X),
      pairedSkewExp_mem_specialOrthogonalGroup X hX
        (Multiplicative.toAdd u)⟩
  map_one' := by
    apply Subtype.ext
    change exp ((0 : ℝ) • X) =
      (1 : Matrix Source48Label Source48Label ℝ)
    exact pairedMatrixExp_zero X
  map_mul' := by
    intro s t
    apply Subtype.ext
    change exp (((Multiplicative.toAdd s) +
      (Multiplicative.toAdd t)) • X) =
      exp ((Multiplicative.toAdd s) • X) *
      exp ((Multiplicative.toAdd t) • X)
    exact pairedMatrixExp_add X
      (Multiplicative.toAdd s) (Multiplicative.toAdd t)

/-- Continuous one-parameter SO(48) homomorphism on the original
paired-Fock 48-real labels. Continuity is inherited from the
same original matrix exponential, not postulated. -/
noncomputable def pairedSkewContinuousOneParameterSpecialOrthogonalHom
    (X : Matrix Source48Label Source48Label ℝ)
    (hX : X.transpose = -X) :
    ContinuousMonoidHom (Multiplicative ℝ)
      (Matrix.specialOrthogonalGroup Source48Label ℝ) :=
  ⟨pairedSkewOneParameterSpecialOrthogonalHom X hX, by
    apply Continuous.subtype_mk
    change Continuous (fun u : Multiplicative ℝ =>
      exp ((Multiplicative.toAdd u) • X))
    exact (pairedMatrixExp_continuous_real X).comp
      (continuous_toAdd (X := ℝ))⟩

/-- The actual matrix of the qualified candidate SO(48) flow. -/
theorem pairedSkewContinuousOneParameterSpecialOrthogonalHom_apply
    (X : Matrix Source48Label Source48Label ℝ)
    (hX : X.transpose = -X) (t : ℝ) :
    ((pairedSkewContinuousOneParameterSpecialOrthogonalHom X hX
      (Multiplicative.ofAdd t)) :
      Matrix Source48Label Source48Label ℝ) =
        exp (t • X) := rfl

/-- Every original normalized paired generator has its
own genuine continuous SO(48) one-parameter homomorphism. -/
noncomputable def normalizedPairedPlaneContinuousOneParameterSpecialOrthogonalHom
    (r s : SpaceIndex) :
    ContinuousMonoidHom (Multiplicative ℝ)
      (Matrix.specialOrthogonalGroup Source48Label ℝ) :=
  pairedSkewContinuousOneParameterSpecialOrthogonalHom
    (normalizedPairedPlane r s)
    (normalizedPairedPlane_transpose r s)

/-- Exact original paired generator evaluation, including
repeated and reversed spatial index cases. -/
theorem normalizedPairedPlaneContinuousOneParameterSpecialOrthogonalHom_apply
    (r s : SpaceIndex) (t : ℝ) :
    ((normalizedPairedPlaneContinuousOneParameterSpecialOrthogonalHom
      r s (Multiplicative.ofAdd t)) :
      Matrix Source48Label Source48Label ℝ) =
        exp (t • normalizedPairedPlane r s) := rfl

/-- Every image under the genuine V9T source so(9) to
original paired so(48) LieHom has an individual continuous
SO(48) one-parameter homomorphism. -/
noncomputable def coordinateToPairedCanonicalContinuousOneParameterSpecialOrthogonalHom
    (A : skewAdjointMatricesLieSubalgebra
      (1 : Matrix SpaceIndex SpaceIndex ℝ)) :
    ContinuousMonoidHom (Multiplicative ℝ)
      (Matrix.specialOrthogonalGroup Source48Label ℝ) := by
  let X : skewAdjointMatricesLieSubalgebra
      (1 : Matrix Source48Label Source48Label ℝ) :=
    coordinateToPairedCanonicalSkewLieHom A
  have hX : (X : Matrix Source48Label Source48Label ℝ).transpose =
      -(X : Matrix Source48Label Source48Label ℝ) := by
    have hm : (X : Matrix Source48Label Source48Label ℝ) ∈
        pairedSkewLieSubalgebra := by
      rw [pairedSkewLieSubalgebra_eq_mathlib]
      exact X.property
    change (X : Matrix Source48Label Source48Label ℝ).transpose =
      -(X : Matrix Source48Label Source48Label ℝ) at hm
    exact hm
  exact pairedSkewContinuousOneParameterSpecialOrthogonalHom
    (X : Matrix Source48Label Source48Label ℝ) hX

/-- Exact original source LieHom image, not a surrogate 48-label
matrix or replacement Lie algebra. -/
theorem coordinateToPairedCanonicalContinuousOneParameterSpecialOrthogonalHom_apply
    (A : skewAdjointMatricesLieSubalgebra
      (1 : Matrix SpaceIndex SpaceIndex ℝ)) (t : ℝ) :
    ((coordinateToPairedCanonicalContinuousOneParameterSpecialOrthogonalHom
      A (Multiplicative.ofAdd t)) :
      Matrix Source48Label Source48Label ℝ) =
        exp (t • ((coordinateToPairedCanonicalSkewLieHom A) :
          Matrix Source48Label Source48Label ℝ)) := rfl

#print axioms pairedSkewOneParameterSpecialOrthogonalHom
#print axioms pairedSkewContinuousOneParameterSpecialOrthogonalHom
#print axioms pairedSkewContinuousOneParameterSpecialOrthogonalHom_apply
#print axioms normalizedPairedPlaneContinuousOneParameterSpecialOrthogonalHom
#print axioms normalizedPairedPlaneContinuousOneParameterSpecialOrthogonalHom_apply
#print axioms coordinateToPairedCanonicalContinuousOneParameterSpecialOrthogonalHom
#print axioms coordinateToPairedCanonicalContinuousOneParameterSpecialOrthogonalHom_apply

end
end FCP.BFSSPairedSpin9Plane
