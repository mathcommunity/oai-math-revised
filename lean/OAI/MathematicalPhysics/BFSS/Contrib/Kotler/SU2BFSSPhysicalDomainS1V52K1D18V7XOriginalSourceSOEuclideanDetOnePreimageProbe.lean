import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7WOriginalSourceSpinQuotientByNegativeCentralProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7LOriginalSourceSOEvenCartanListProbe
import Mathlib.LinearAlgebra.Determinant

/-!
K1D18V7X — EVERY native SAME-48-label Euclidean linear isometry
with determinant +1 has a preimage in the GENUINE original
source48SpecialOrthogonalWitnessGL group under the strictly
accepted original source-SO Euclidean MonoidHom.

Already accepted:
* V7I: any genuine native Euclidean linear isometry has a
  zero-free bounded ordered list of norm-one hyperplane reflections.
* V7L: determinant +1 of such a list implies EVEN list length.
* V7Q: each even unit-normal list is the Euclidean image of an
  ACTUAL original Clifford spinGroup source48Quadratic word.
* K1D18S/V7P: that exact word's ORIGINAL sourceSO action
  transports by the unchanged original sourceSO-to-Euclidean hom.

This is SURJECTIVITY ON THE DETERMINANT-ONE NATIVE TARGET, not
onto all orthogonal isometries (determinant -1 is excluded).
A later theorem must separately package the original sourceSO
as an algebraic isomorphism onto the true Euclidean det-one
subgroup using V7E and V7R. No topological quotient, canonical
standard SO48 Lie topology, local homeomorphism, covering,
global Spin9 lift or BFSS spectral result is claimed.
One theorem CANDIDATE pending strict source-exact CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7X
noncomputable section
open FCP.BFSSS1V0
open Submodule

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev SourceSO :=
  FCP.BFSSS1V52K1D18R.source48SpecialOrthogonalWitnessGL
private abbrev Euc48 := EuclideanSpace ℝ Source48Label
private abbrev sourceSOHom : spinGroup Q →* SourceSO :=
  FCP.BFSSS1V52K1D18S.originalSourceSpin48SpecialOrthogonalWitnessRepresentation
private abbrev transport : SourceSO →* (Euc48 ≃ₗᵢ[ℝ] Euc48) :=
  FCP.BFSSS1V52K1D18V7P.originalSourceSO_toEuclideanHom

/-- Every actual SAME-48-label Euclidean norm-preserving linear
equivalence with determinant +1 is the transported image of
some ORIGINAL sourceSO element. The proof exhibits an actual
original Clifford Spin word, but does not classify topology. -/
theorem euclideanDetOne_hasOriginalSourceSOPreimage
    (φ : Euc48 ≃ₗᵢ[ℝ] Euc48)
    (hφ : LinearEquiv.det φ.toLinearEquiv = 1) :
    ∃ g : SourceSO, transport g = φ := by
  obtain ⟨unitNormals, hall, _hlen, hfactor⟩ :=
    FCP.BFSSS1V52K1D18V7I.originalSourceEuclidean_Cartan_zeroFreeUnitNormals φ
  have hφval : ((LinearEquiv.det φ.toLinearEquiv : ℝˣ) : ℝ) = 1 :=
    congrArg (fun z : ℝˣ => (z : ℝ)) hφ
  have hφdet : LinearMap.det φ.toLinearMap = 1 := by
    simpa only [LinearEquiv.coe_det] using hφval
  have hdet :
      LinearMap.det
        (((unitNormals.map fun u => (ℝ ∙ u)ᗮ.reflection).prod).toLinearMap) = 1 := by
    rw [← hfactor]
    exact hφdet
  have heven : Even unitNormals.length :=
    FCP.BFSSS1V52K1D18V7L.euclideanUnitReflectionList_even_of_det_one
      unitNormals hall hdet
  obtain ⟨s, hs⟩ :=
    FCP.BFSSS1V52K1D18V7Q.originalSourceEvenUnitList_hasSpinWordImage
      unitNormals hall heven
  exact ⟨sourceSOHom s, hs.trans hfactor.symm⟩

#print axioms euclideanDetOne_hasOriginalSourceSOPreimage

end
end FCP.BFSSS1V52K1D18V7X
