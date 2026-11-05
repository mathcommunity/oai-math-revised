import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7TOriginalSourceSpinSOEveryFiberTwoSignsProbe
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
K1D18V7U — EXACT algebraic first-isomorphism theorem for the
genuine ORIGINAL same-48-label Clifford Spin-to-sourceSO map.

Accepted V7S: unconditional surjectivity of the unchanged original
spinGroup source48Quadratic representation onto the ACTUAL original
source48SpecialOrthogonalWitnessGL subgroup. Accepted K1D18S:
its kernel is exactly the original two-sign central set. Accepted
V7T: EACH target has two distinct actual original Spin preimages.

The pinned Mathlib quotientKerEquivOfSurjective theorem supplies the
canonical quotient-group isomorphism with NO invented sourceSO model.
The second root proves the quotient map on actual source Spin
elements agrees with the original sourceSO representation. No
topological quotient, covering theorem, local triviality, standard
SO(48) Lie topology identification, global Spin9 lift or physical
BFSS spectral claim is asserted. Both new roots CANDIDATE until
fresh warning-as-error source compilation and independent axiom audit.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7U
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev SourceSO :=
  FCP.BFSSS1V52K1D18R.source48SpecialOrthogonalWitnessGL
private abbrev sourceSOHom : spinGroup Q →* SourceSO :=
  FCP.BFSSS1V52K1D18S.originalSourceSpin48SpecialOrthogonalWitnessRepresentation

/-- The ORIGINAL Spin group modulo the kernel of the actual
original source-SO representation is multiplicatively isomorphic
to that ACTUAL source-SO group. The kernel is the accepted exact
two-sign subgroup; no topological covering conclusion follows. -/
noncomputable def originalSourceSpin48SO_quotientKernelMulEquiv :
    (spinGroup Q ⧸ sourceSOHom.ker) ≃* SourceSO :=
  QuotientGroup.quotientKerEquivOfSurjective sourceSOHom
    FCP.BFSSS1V52K1D18V7S.originalSourceSpin48SourceSO_surjective

/-- This IS the original source Clifford Spin-to-sourceSO action
on each represented original Spin element, not a new group map. -/
theorem originalSourceSpin48SO_quotientKernelMulEquiv_mk
    (s : spinGroup Q) :
    originalSourceSpin48SO_quotientKernelMulEquiv
      (QuotientGroup.mk s : spinGroup Q ⧸ sourceSOHom.ker) =
        sourceSOHom s := by
  rfl

#print axioms originalSourceSpin48SO_quotientKernelMulEquiv
#print axioms originalSourceSpin48SO_quotientKernelMulEquiv_mk

end
end FCP.BFSSS1V52K1D18V7U
