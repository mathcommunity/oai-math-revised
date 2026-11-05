import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9ContinuousOrthogonalFlowProbe
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Constructions

/-!
K1D18V9Z — genuine continuous one-parameter orthogonal monoid homs
using the exact original 48-label paired-Fock carrier.

The previously accepted V9X typed MonoidHom and V9Y real
parameter continuity theorem jointly construct continuous
homomorphisms, rather than standalone continuity predicates.

No determinant-one, globally integrated Spin(9), Spin(48) lift,
covering, or BFSS physical claim is asserted.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open NormedSpace

/-- Every source-exact real skew matrix generates a continuous
one-parameter homomorphism into the actual orthogonal group on
the original paired-Fock 48 real labels. -/
noncomputable def pairedSkewContinuousOneParameterOrthogonalHom
    (X : Matrix Source48Label Source48Label ℝ)
    (hX : X.transpose = -X) :
    ContinuousMonoidHom (Multiplicative ℝ)
      (Matrix.orthogonalGroup Source48Label ℝ) :=
  ⟨pairedSkewOneParameterOrthogonalHom X hX, by
    have h := (pairedSkewOneParameterOrthogonalHom_continuous_real X hX).comp
      (continuous_toAdd (X := ℝ))
    change Continuous (fun u : Multiplicative ℝ =>
      pairedSkewOneParameterOrthogonalHom X hX
        (Multiplicative.ofAdd (Multiplicative.toAdd u))) at h
    exact h.congr (fun u => by simp only [ofAdd_toAdd, MonoidHom.toFun_eq_coe])⟩

/-- Exact original paired matrix evaluation of the continuous hom. -/
theorem pairedSkewContinuousOneParameterOrthogonalHom_apply
    (X : Matrix Source48Label Source48Label ℝ)
    (hX : X.transpose = -X) (t : ℝ) :
    ((pairedSkewContinuousOneParameterOrthogonalHom X hX
      (Multiplicative.ofAdd t)) : Matrix Source48Label Source48Label ℝ) =
      exp (t • X) := rfl

/-- Each original normalized paired-Fock plane admits a
continuous one-parameter orthogonal homomorphism. -/
noncomputable def normalizedPairedPlaneContinuousOneParameterOrthogonalHom
    (r s : SpaceIndex) :
    ContinuousMonoidHom (Multiplicative ℝ)
      (Matrix.orthogonalGroup Source48Label ℝ) :=
  ⟨normalizedPairedPlaneOneParameterOrthogonalHom r s, by
    have h :=
      (normalizedPairedPlaneOneParameterOrthogonalHom_continuous_real r s).comp
        (continuous_toAdd (X := ℝ))
    change Continuous (fun u : Multiplicative ℝ =>
      normalizedPairedPlaneOneParameterOrthogonalHom r s
        (Multiplicative.ofAdd (Multiplicative.toAdd u))) at h
    exact h.congr (fun u => by simp only [ofAdd_toAdd, MonoidHom.toFun_eq_coe])⟩

/-- Exact original normalized plane exponential as a
continuous orthogonal-hom matrix evaluation. -/
theorem normalizedPairedPlaneContinuousOneParameterOrthogonalHom_apply
    (r s : SpaceIndex) (t : ℝ) :
    ((normalizedPairedPlaneContinuousOneParameterOrthogonalHom r s
      (Multiplicative.ofAdd t)) : Matrix Source48Label Source48Label ℝ) =
      exp (t • normalizedPairedPlane r s) := rfl

/-- For every image of the canonical source-exact LieHom,
the corresponding individual one-parameter flow defines
a continuous homomorphism into the original orthogonal group. -/
noncomputable def coordinateToPairedCanonicalContinuousOneParameterOrthogonalHom
    (A : skewAdjointMatricesLieSubalgebra
      (1 : Matrix SpaceIndex SpaceIndex ℝ)) :
    ContinuousMonoidHom (Multiplicative ℝ)
      (Matrix.orthogonalGroup Source48Label ℝ) :=
  ⟨coordinateToPairedCanonicalOneParameterOrthogonalHom A, by
    have h :=
      (coordinateToPairedCanonicalOneParameterOrthogonalHom_continuous_real A).comp
        (continuous_toAdd (X := ℝ))
    change Continuous (fun u : Multiplicative ℝ =>
      coordinateToPairedCanonicalOneParameterOrthogonalHom A
        (Multiplicative.ofAdd (Multiplicative.toAdd u))) at h
    exact h.congr (fun u => by simp only [ofAdd_toAdd, MonoidHom.toFun_eq_coe])⟩

/-- The canonical LieHom-image continuous one-parameter flow
uses exactly its original source 48×48 matrix exponential. -/
theorem coordinateToPairedCanonicalContinuousOneParameterOrthogonalHom_apply
    (A : skewAdjointMatricesLieSubalgebra
      (1 : Matrix SpaceIndex SpaceIndex ℝ)) (t : ℝ) :
    ((coordinateToPairedCanonicalContinuousOneParameterOrthogonalHom A
      (Multiplicative.ofAdd t)) : Matrix Source48Label Source48Label ℝ) =
      exp (t • ((coordinateToPairedCanonicalSkewLieHom A) :
        Matrix Source48Label Source48Label ℝ)) := rfl

#print axioms pairedSkewContinuousOneParameterOrthogonalHom
#print axioms pairedSkewContinuousOneParameterOrthogonalHom_apply
#print axioms normalizedPairedPlaneContinuousOneParameterOrthogonalHom
#print axioms normalizedPairedPlaneContinuousOneParameterOrthogonalHom_apply
#print axioms coordinateToPairedCanonicalContinuousOneParameterOrthogonalHom
#print axioms coordinateToPairedCanonicalContinuousOneParameterOrthogonalHom_apply

end
end FCP.BFSSPairedSpin9Plane
