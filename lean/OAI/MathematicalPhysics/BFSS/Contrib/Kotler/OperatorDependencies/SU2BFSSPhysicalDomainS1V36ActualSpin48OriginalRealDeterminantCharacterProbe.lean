import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V35ActualSpin48RealAutomorphismGroupHomProbe
import Mathlib.LinearAlgebra.Determinant

/-!
S1V36 — the GENUINE Clifford Spin48 original source-real determinant
CHARACTER, not yet its orientation-triviality theorem.

The exact accepted S1V35 group hom maps every genuine source
spinGroup source48Quadratic element to a REAL automorphism of the
original Fin24 × Fin2 → ℝ source vector. Pinned Mathlib's
LinearEquiv.det is an actual group hom into ℝˣ, and this module
instantiates its composition with the accepted source action.

These are THREE UNCOMPILED proof roots until source-pinned strict CI.
Their mathematical ceiling is a determinant *character*, not the
separate claim that every determinant equals +1. In particular,
do NOT identify a merely Q-preserving representation with SO48,
or infer the topological Spin double-cover/normalized SU2 global lift.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V36
noncomputable section

open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- A multiplicative REAL determinant character of the ACTUAL
original source Clifford Spin48 group action, valued in ℝˣ.
This is NOT yet the constant character 1. -/
noncomputable def sourceSpin48OriginalRealDetCharacter :
    spinGroup Q →* ℝˣ :=
  (LinearEquiv.det :
    (Source48Vector ≃ₗ[ℝ] Source48Vector) →* ℝˣ).comp
      FCP.BFSSS1V35.sourceSpin48LinearEquivHom

/-- The character is the concrete real determinant of the original
source48 linear automorphism, rather than a formal auxiliary character. -/
theorem sourceSpin48OriginalRealDetCharacter_value (s : spinGroup Q) :
    (sourceSpin48OriginalRealDetCharacter s : ℝ) =
      LinearMap.det
        ((FCP.BFSSS1V34.sourceSpin48LinearEquiv s :
          Source48Vector ≃ₗ[ℝ] Source48Vector) :
          Source48Vector →ₗ[ℝ] Source48Vector) := by
  change (LinearEquiv.det (FCP.BFSSS1V34.sourceSpin48LinearEquiv s) : ℝ) =
    LinearMap.det
      ((FCP.BFSSS1V34.sourceSpin48LinearEquiv s :
        Source48Vector ≃ₗ[ℝ] Source48Vector) :
        Source48Vector →ₗ[ℝ] Source48Vector)
  exact LinearEquiv.coe_det (FCP.BFSSS1V34.sourceSpin48LinearEquiv s)

/-- Multiplicativity for ALL genuine source Spin48 elements, in
the ORIGINAL Clifford group order, with no parity assumption. -/
theorem sourceSpin48OriginalRealDetCharacter_mul
    (s t : spinGroup Q) :
    sourceSpin48OriginalRealDetCharacter (s * t) =
      sourceSpin48OriginalRealDetCharacter s *
        sourceSpin48OriginalRealDetCharacter t := by
  exact map_mul sourceSpin48OriginalRealDetCharacter s t

#print axioms sourceSpin48OriginalRealDetCharacter
#print axioms sourceSpin48OriginalRealDetCharacter_value
#print axioms sourceSpin48OriginalRealDetCharacter_mul

end
end FCP.BFSSS1V36
