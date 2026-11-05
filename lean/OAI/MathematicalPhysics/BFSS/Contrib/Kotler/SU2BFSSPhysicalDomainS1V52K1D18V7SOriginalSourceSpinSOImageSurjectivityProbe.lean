import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7ROriginalSourceSOEuclideanTransportInjectivityProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7LOriginalSourceSOEvenCartanListProbe

/-!
K1D18V7S — direct source-exact SURJECTIVITY candidate for the
original Clifford Spin(48) homomorphism onto the genuine ORIGINAL
source48SpecialOrthogonalWitnessGL subgroup of the ORIGINAL
48-real source-vector linear equivalence group.

Use EXACT prior accepted declarations, without a generation
hypothesis:
* V7L: every actual sourceSO element admits an EXACT ordered
  even-length norm-one Euclidean hyperplane-reflection list
  in the original SAME 48-label coordinates.
* V7Q: every such even list is the transported image of
  some actual original Clifford spinGroup source48Quadratic
  element under the accepted ORIGINAL source Spin-to-SO hom.
* V7R: the accepted original sourceSO to same-label Euclidean
  transport is INJECTIVE.

This yields a genuine preimage of any original sourceSO element.
It does NOT identify sourceSO with a separately defined standard
SO(48) Lie group, establish that the hom is a topological covering,
construct a global Spin(9) representation, or prove BFSS spectral
existence. Those obligations remain independent and unproved.
One theorem CANDIDATE until source-pinned strict verification.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7S
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev SourceSO :=
  FCP.BFSSS1V52K1D18R.source48SpecialOrthogonalWitnessGL
private abbrev Euc48 := EuclideanSpace ℝ Source48Label
private abbrev sourceSOHom : spinGroup Q →* SourceSO :=
  FCP.BFSSS1V52K1D18S.originalSourceSpin48SpecialOrthogonalWitnessRepresentation
private abbrev transport : SourceSO →* (Euc48 ≃ₗᵢ[ℝ] Euc48) :=
  FCP.BFSSS1V52K1D18V7P.originalSourceSO_toEuclideanHom

/-- UNCONDITIONAL surjectivity onto the ACTUAL original
source48SpecialOrthogonalWitnessGL subgroup. This is source
Spin48, source Q, source labels and the existing genuine
spinGroup-to-sourceSO map, not any auxiliary invented action.
There is no Cartan generation hypothesis or axiom here. -/
theorem originalSourceSpin48SourceSO_surjective :
    Function.Surjective sourceSOHom := by
  intro g
  obtain ⟨unitNormals, hall, _hlen, heven, hfactor⟩ :=
    FCP.BFSSS1V52K1D18V7L.originalSourceSO_has_evenUnitCartanFactorization g
  obtain ⟨s, hs⟩ :=
    FCP.BFSSS1V52K1D18V7Q.originalSourceEvenUnitList_hasSpinWordImage
      unitNormals hall heven
  refine ⟨s, ?_⟩
  apply FCP.BFSSS1V52K1D18V7R.originalSourceSO_toEuclideanHom_injective
  exact hs.trans hfactor.symm

#print axioms originalSourceSpin48SourceSO_surjective

end
end FCP.BFSSS1V52K1D18V7S
