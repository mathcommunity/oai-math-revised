import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F11OriginalNativeSixteenSpin48FockTwoSidedUnitarityProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F6OriginalBlockQuaternionFockStarAdjointBridgeProbe

/-!
S1V52L9E5F12 — STAGED / UNQUALIFIED, two roots.

Original actual-source proof that Clifford star intertwines with
the original Fermion2 Fock Hilbert adjoint on arbitrary FINITE
ORDERED products of genuine native SU2→Spin48 source blocks,
and hence on the EXACT original canonical sixteen-block Spin48
gauge image. The global all-Clifford star-hom shortcut is false
for odd Clifford generators and is NOT made here.

Use accepted F6 individual actual quaternion star transport,
accepted F1 conditional multiplicative closure, and F2 typed
identity/base case. No commutative reordering, hypothetical
global Spin48 representation, physical gauge implementer
identification, or BFSS spectral assertion.
-/

set_option autoImplicit false
set_option maxHeartbeats 360000

namespace FCP.BFSSS1V52L9E5F12
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52C1
open FCP.BFSSS1V52L7C7
open FCP.BFSSS1V52L8E
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5F1
open FCP.BFSSS1V52L9E5F2
open FCP.BFSSS1V52L9E5F6

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Actual Clifford star on an arbitrary ordered product of
native genuine original Spin48 blocks is sent to the genuine
original Fock Hilbert adjoint, for every original native SU2
element. Block order is preserved on both sides before star. -/
theorem originalNativeSpinBlockList_star_fock_adjoint
    (g : GaugeGroup 2) (xs : List RealSpinBlock) :
    originalFockCliffordAlgHom
      (star ((((xs.map (fun α => originalNativeGaugeSpinHom α g)).prod :
        spinGroup Q) : C))) =
      star (originalFockCliffordAlgHom
        ((((xs.map (fun α => originalNativeGaugeSpinHom α g)).prod :
          spinGroup Q) : C))) := by
  induction xs with
  | nil =>
      change originalFockCliffordAlgHom (star (1 : C)) =
        star (originalFockCliffordAlgHom (1 : C))
      exact originalFockCliffordAlgHom_star_one
  | cons α xs ih =>
      have hblock :
          originalFockCliffordAlgHom
            (star (((originalNativeGaugeSpinHom α g : spinGroup Q) : C))) =
          star (originalFockCliffordAlgHom
            (((originalNativeGaugeSpinHom α g : spinGroup Q) : C))) := by
        rw [originalNativeGaugeSpinHom_coe α g]
        exact originalFockCliffordAlgHom_star_sourceQuaternion
          α (originalNativeQuaternionCoords g)
      change originalFockCliffordAlgHom
        (star ((((originalNativeGaugeSpinHom α g : spinGroup Q) : C)) *
          ((((xs.map (fun β => originalNativeGaugeSpinHom β g)).prod :
            spinGroup Q) : C)))) =
        star (originalFockCliffordAlgHom
          ((((originalNativeGaugeSpinHom α g : spinGroup Q) : C)) *
            ((((xs.map (fun β => originalNativeGaugeSpinHom β g)).prod :
              spinGroup Q) : C))))
      exact originalFockCliffordAlgHom_star_mul_of
        (((originalNativeGaugeSpinHom α g : spinGroup Q) : C))
        ((((xs.map (fun β => originalNativeGaugeSpinHom β g)).prod :
          spinGroup Q) : C))
        hblock ih

/-- Actual original sixteen-block native SU2→Spin48 Clifford
star is mapped to the genuine Hilbert adjoint of the single
corresponding original Fermion2 Fock operator, *not* because
the algebra map is globally star preserving. -/
theorem originalNativeSixteenSpin48_star_fock_adjoint
    (g : GaugeGroup 2) :
    originalFockCliffordAlgHom
      (star (((originalNativeSixteenSpinHom g : spinGroup Q) : C))) =
      star (originalFockCliffordAlgHom
        (((originalNativeSixteenSpinHom g : spinGroup Q) : C))) := by
  rw [originalNativeSixteenSpinHom_apply]
  exact originalNativeSpinBlockList_star_fock_adjoint
    g originalNativeSixteenSpinBlocks

#print axioms originalNativeSpinBlockList_star_fock_adjoint
#print axioms originalNativeSixteenSpin48_star_fock_adjoint

end
end FCP.BFSSS1V52L9E5F12
