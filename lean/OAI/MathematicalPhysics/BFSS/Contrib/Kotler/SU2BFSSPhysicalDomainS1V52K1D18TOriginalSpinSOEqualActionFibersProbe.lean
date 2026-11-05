import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18SOriginalSpinSpecialOrthogonalWitnessHomKernelProbe

/-!
K1D18T — exact algebraic fibers of the already-qualified original
Spin48 source-Q special-orthogonal witness group homomorphism.
No assumption of surjectivity, canonical matrix SO presentation,
topological covering, global Spin9 covariance or BFSS spectrum.
Every source identity is the existing accepted one.
Research candidate until independent exact-axiom strict gate.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18T
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev SourceSO :=
  FCP.BFSSS1V52K1D18R.source48SpecialOrthogonalWitnessGL
private abbrev sourceSOHom : spinGroup Q →* SourceSO :=
  FCP.BFSSS1V52K1D18S.originalSourceSpin48SpecialOrthogonalWitnessRepresentation

/-- Equality of two genuine ORIGINAL source Spin48 actions
is exactly equality up to multiplication by the negative central
Spin element. This is a statement about fibers, NOT covering. -/
theorem originalSourceSpin48SO_equal_action_iff_two_sign_fiber
    (s t : spinGroup Q) :
    sourceSOHom s = sourceSOHom t ↔
      s = t ∨ s = FCP.BFSSS1V52K1D11.originalSourceNegativeCentral * t := by
  constructor
  · intro h
    have hker : sourceSOHom (s * t⁻¹) = 1 := by
      calc
        sourceSOHom (s * t⁻¹) =
            sourceSOHom s * sourceSOHom (t⁻¹) :=
          map_mul sourceSOHom s (t⁻¹)
        _ = sourceSOHom s * (sourceSOHom t)⁻¹ := by rw [map_inv]
        _ = 1 := by rw [h, mul_inv_cancel]
    have htwo :
        s * t⁻¹ = 1 ∨
          s * t⁻¹ = FCP.BFSSS1V52K1D11.originalSourceNegativeCentral :=
      (((FCP.BFSSS1V52K1D18S.originalSourceSpin48SpecialOrthogonalWitnessRepresentation_eq_one_iff_original
        (s * t⁻¹)).trans
        (FCP.BFSSS1V52K1D14.originalSourceSpin48LinearRepresentation_eq_one_iff_two_signs
          (s * t⁻¹)))).mp hker
    rcases htwo with hOne | hNeg
    · left
      calc
        s = (s * t⁻¹) * t := by rw [mul_assoc, inv_mul_cancel, mul_one]
        _ = t := by rw [hOne, one_mul]
    · right
      calc
        s = (s * t⁻¹) * t := by rw [mul_assoc, inv_mul_cancel, mul_one]
        _ = FCP.BFSSS1V52K1D11.originalSourceNegativeCentral * t := by rw [hNeg]
  · intro h
    rcases h with hSame | hNeg
    · exact congrArg sourceSOHom hSame
    · have hCentralImage :
          sourceSOHom FCP.BFSSS1V52K1D11.originalSourceNegativeCentral = 1 :=
        (((FCP.BFSSS1V52K1D18S.originalSourceSpin48SpecialOrthogonalWitnessRepresentation_eq_one_iff_original
          FCP.BFSSS1V52K1D11.originalSourceNegativeCentral).trans
          (FCP.BFSSS1V52K1D14.originalSourceSpin48LinearRepresentation_eq_one_iff_two_signs
            FCP.BFSSS1V52K1D11.originalSourceNegativeCentral))).mpr (Or.inr rfl)
      calc
        sourceSOHom s =
            sourceSOHom (FCP.BFSSS1V52K1D11.originalSourceNegativeCentral * t) :=
          congrArg sourceSOHom hNeg
        _ = sourceSOHom FCP.BFSSS1V52K1D11.originalSourceNegativeCentral *
              sourceSOHom t :=
          map_mul sourceSOHom FCP.BFSSS1V52K1D11.originalSourceNegativeCentral t
        _ = sourceSOHom t := by rw [hCentralImage, one_mul]

/-- Noninjectivity of the original source SO-witness map follows
from its exact two-element fibers, not from any global topology. -/
theorem originalSourceSpin48SO_not_injective :
    ¬ Function.Injective sourceSOHom := by
  intro hinj
  have hpair :
      sourceSOHom FCP.BFSSS1V52K1D11.originalSourceNegativeCentral =
        sourceSOHom 1 :=
    (originalSourceSpin48SO_equal_action_iff_two_sign_fiber
      FCP.BFSSS1V52K1D11.originalSourceNegativeCentral 1).mpr
      (Or.inr (by simp only [mul_one]))
  have hsign :
      FCP.BFSSS1V52K1D11.originalSourceNegativeCentral =
        (1 : spinGroup Q) :=
    hinj hpair
  exact FCP.BFSSS1V52K1D11.originalSourceSpin48_one_ne_negativeCentral
    hsign.symm

#print axioms originalSourceSpin48SO_equal_action_iff_two_sign_fiber
#print axioms originalSourceSpin48SO_not_injective

end
end FCP.BFSSS1V52K1D18T
