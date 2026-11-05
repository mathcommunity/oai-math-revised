import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V46OriginalSpinLipschitzRestrictionBridgeProbe
import Mathlib.Algebra.Algebra.IsSimpleRing

/-!
S1V47 — exact original real Spin48 orientation.

The source-specific scalar faithfulness is derived from the accepted
original 48-real Clifford generator injection and the pinned ℝ-field
algebra structure. Universal Lipschitz parity is S1V45; the TRUE
Spin-only source determinant equality with restricted Lipschitz
character is S1V46. No generic arbitrary-ring Clifford scalar
faithfulness is assumed, nor any global SU(2) lift or spectral theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V47
noncomputable section

open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev A := CliffordAlgebra Q
private abbrev j := FCP.BFSSS1V46.sourceSpin48ToActualLipschitz
private abbrev δ := FCP.BFSSS1V41.sourceLipschitz48OriginalRealDetCharacter

/-- Nontriviality of the EXACT original finite-48-real source Clifford
algebra, from the previously kernel-accepted injective degree-one
source Clifford map, not from a universal scalar embedding axiom. -/
theorem source48OriginalClifford_nontrivial : Nontrivial A :=
  FCP.BFSSS1V30.source48_cliffordGenerator_injective.nontrivial

/-- True invertible real scalars inject into actual source Clifford
UNITS, using field-to-nontrivial-algebra injectivity. -/
theorem source48OriginalRealScalarUnits_injective :
    Function.Injective FCP.BFSSS1V44.source48RealScalarOnUnits := by
  let : Nontrivial A := source48OriginalClifford_nontrivial
  unfold FCP.BFSSS1V44.source48RealScalarOnUnits
  exact Units.map_injective (FaithfulSMul.algebraMap_injective ℝ A)

/-- Universal parity plus genuine Spin evenness force the LIPSCHITZ
determinant character of the SAME original Spin element to equal 1.
All cancellation occurs in genuine Clifford units, then uses the
source-qualified faithful REAL scalar unit embedding. -/
theorem sourceSpin48ActualLipschitzDetCharacter_one
    (s : spinGroup Q) : δ (j s) = 1 := by
  let x : lipschitzGroup Q := j s
  have hs : FCP.BFSSS1V44.source48GradeOnUnits (x : Aˣ) = (x : Aˣ) := by
    apply Units.ext
    change CliffordAlgebra.involute (s : A) = (s : A)
    exact spinGroup.involute_eq s.property
  have hp :
      FCP.BFSSS1V44.source48GradeOnUnits (x : Aˣ) =
        FCP.BFSSS1V44.source48RealScalarOnUnits (δ x) * (x : Aˣ) :=
    (FCP.BFSSS1V44.source48LipschitzGradeDetParity_iff_units x).1
      (FCP.BFSSS1V45.source48ActualLipschitz_gradeDetParity_all x)
  have hm :
      FCP.BFSSS1V44.source48RealScalarOnUnits (δ x) * (x : Aˣ) =
        (1 : Aˣ) * (x : Aˣ) := by
    rw [← hp, hs, one_mul]
  have hc :
      FCP.BFSSS1V44.source48RealScalarOnUnits (δ x) = 1 :=
    mul_right_cancel hm
  have hd : δ x = 1 := by
    apply source48OriginalRealScalarUnits_injective
    simpa only [map_one] using hc
  exact hd

/-- Original S1V36 Spin-only determinant character is the constant +1.
This concludes ONLY actual source Spin48 ORIENTATION, not a global
SU2 lift, covering or a BFSS mass gap. -/
theorem sourceSpin48OriginalRealDetCharacter_one
    (s : spinGroup Q) :
    FCP.BFSSS1V36.sourceSpin48OriginalRealDetCharacter s = 1 := by
  rw [FCP.BFSSS1V46.sourceSpin48OriginalRealDetCharacter_eq_lipschitz]
  exact sourceSpin48ActualLipschitzDetCharacter_one s

#print axioms source48OriginalClifford_nontrivial
#print axioms source48OriginalRealScalarUnits_injective
#print axioms sourceSpin48ActualLipschitzDetCharacter_one
#print axioms sourceSpin48OriginalRealDetCharacter_one

end
end FCP.BFSSS1V47
