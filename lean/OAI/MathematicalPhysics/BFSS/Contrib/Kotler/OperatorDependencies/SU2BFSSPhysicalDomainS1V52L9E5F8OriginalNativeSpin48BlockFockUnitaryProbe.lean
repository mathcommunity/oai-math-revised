import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F7OriginalBlockQuaternionFockTwoSidedUnitaryProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L7C7OriginalNativeEulerWitnessAndSpinHomProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52C1OriginalNativeGaugeQuaternionCoordinatesProbe

/-!
S1V52L9E5F8 — STAGED ONLY, NOT QUALIFIED, NO CI.

This is a deliberate second bridge from the SOURCE-QUATERNION
Fock-unitarity obligations (pending F7 strict qualification)
to the ACTUAL NATIVE GaugeGroup 2 →* spinGroup source48Quadratic
individual block hom `originalNativeGaugeSpinHom α`.
The accepted original L7C7 coercion theorem identifies that
exact Spin48 element with the source quaternion polynomial
whose coordinates are originalNativeQuaternionCoords g.
Original C1 establishes its exact real source norm equals one.

Do not claim unitary image of the full sixteen-block Spin48
lift until an additional ordered-product proof, and do not
identify this with the original physical gauge implementation
without a separately strict theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 320000

namespace FCP.BFSSS1V52L9E5F8
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52C1
open FCP.BFSSS1V52L7C7
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5F7

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- Actual Fock Hilbert adjoint is a LEFT inverse for the
original native block Spin48 image of any original GaugeGroup 2
element, via its actual source Clifford quaternion coercion. -/
theorem originalNativeBlockSpin48Fock_adjoint_mul
    (α : RealSpinBlock) (g : GaugeGroup 2) :
    star (originalFockCliffordAlgHom
      (((originalNativeGaugeSpinHom α g : spinGroup Q) : C))) *
      originalFockCliffordAlgHom
        (((originalNativeGaugeSpinHom α g : spinGroup Q) : C)) =
      (1 : FockOp) := by
  rw [originalNativeGaugeSpinHom_coe α g]
  exact originalFockBlockQuaternion_adjoint_mul
    α (originalNativeQuaternionCoords g)
    (originalNativeQuaternion_norm_one g)

/-- Actual Fock Hilbert adjoint is a RIGHT inverse for the
original native block Spin48 image of any original GaugeGroup 2
element. -/
theorem originalNativeBlockSpin48Fock_mul_adjoint
    (α : RealSpinBlock) (g : GaugeGroup 2) :
    originalFockCliffordAlgHom
      (((originalNativeGaugeSpinHom α g : spinGroup Q) : C)) *
      star (originalFockCliffordAlgHom
        (((originalNativeGaugeSpinHom α g : spinGroup Q) : C))) =
      (1 : FockOp) := by
  rw [originalNativeGaugeSpinHom_coe α g]
  exact originalFockBlockQuaternion_mul_adjoint
    α (originalNativeQuaternionCoords g)
    (originalNativeQuaternion_norm_one g)

#print axioms originalNativeBlockSpin48Fock_adjoint_mul
#print axioms originalNativeBlockSpin48Fock_mul_adjoint

end
end FCP.BFSSS1V52L9E5F8
