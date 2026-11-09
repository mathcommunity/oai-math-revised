import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7SOriginalSourceSpinSOImageSurjectivityProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18TOriginalSpinSOEqualActionFibersProbe

/-!
K1D18V7T — every fiber of the ORIGINAL Spin(48) to original
sourceSO representation is an ACTUAL two-distinct-sign fiber.

Strictly accepted V7S gives unconditional original source
spinGroup source48Quadratic to source48SpecialOrthogonalWitnessGL
surjectivity, with EXACT original Fin24 × Fin2 label order.
Strictly accepted K1D18T gives equality of original sourceSO
images iff the original spin elements differ by multiplication
by the genuine negative central source Spin element.
Strictly accepted K1D11 gives 1 != this central negative element.

We combine these previously accepted results into an explicit
every-target set equality and two distinct genuine preimages.
No supplementary Cartan-generation assumption, new quadratic
form, new sourceSO, covering-space topology, global Spin(9)
lift or physical BFSS spectral existence is asserted.
Both roots are CANDIDATES pending source-exact strict CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7T
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev SourceSO :=
  FCP.BFSSS1V52K1D18R.source48SpecialOrthogonalWitnessGL
private abbrev sourceSOHom : spinGroup Q →* SourceSO :=
  FCP.BFSSS1V52K1D18S.originalSourceSpin48SpecialOrthogonalWitnessRepresentation
private abbrev negativeCentral : spinGroup Q :=
  FCP.BFSSS1V52K1D11.originalSourceNegativeCentral

/-- Every actual ORIGINAL sourceSO target has an explicit fiber
set consisting exactly of the two existing original Spin
central-sign translates of one genuine preimage. This uses
V7S actual surjectivity and K1D18T exact fiber equivalence,
not any topological covering property. -/
theorem originalSourceSpin48SO_everyFiber_eq_twoSignSet
    (g : SourceSO) :
    ∃ s : spinGroup Q,
      sourceSOHom s = g ∧
      {t : spinGroup Q | sourceSOHom t = g} =
        ({s, negativeCentral * s} : Set (spinGroup Q)) := by
  obtain ⟨s, hs⟩ :=
    FCP.BFSSS1V52K1D18V7S.originalSourceSpin48SourceSO_surjective g
  refine ⟨s, hs, ?_⟩
  ext t
  change (sourceSOHom t = g) ↔ (t = s ∨ t = negativeCentral * s)
  rw [← hs]
  exact FCP.BFSSS1V52K1D18T.originalSourceSpin48SO_equal_action_iff_two_sign_fiber t s

/-- The two original Spin source-Q preimages are actually
DISTINCT, because the accepted original negative central
element is not the identity. This is algebraic two-to-one
fiber cardinality, not a topological covering. -/
theorem originalSourceSpin48SO_everyFiber_has_twoDistinctPreimages
    (g : SourceSO) :
    ∃ s : spinGroup Q,
      sourceSOHom s = g ∧
      sourceSOHom (negativeCentral * s) = g ∧
      negativeCentral * s ≠ s := by
  obtain ⟨s, hs⟩ :=
    FCP.BFSSS1V52K1D18V7S.originalSourceSpin48SourceSO_surjective g
  refine ⟨s, hs, ?_, ?_⟩
  · rw [← hs]
    exact (FCP.BFSSS1V52K1D18T.originalSourceSpin48SO_equal_action_iff_two_sign_fiber
      (negativeCentral * s) s).mpr (Or.inr rfl)
  · intro h
    have hsign : negativeCentral = (1 : spinGroup Q) := by
      apply mul_right_cancel (b := s)
      simpa only [one_mul] using h
    exact FCP.BFSSS1V52K1D11.originalSourceSpin48_one_ne_negativeCentral
      hsign.symm

#print axioms originalSourceSpin48SO_everyFiber_eq_twoSignSet
#print axioms originalSourceSpin48SO_everyFiber_has_twoDistinctPreimages

end
end FCP.BFSSS1V52K1D18V7T
