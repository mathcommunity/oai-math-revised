import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F10OriginalNativeSixteenSpin48FockOrderedProductBridgeProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F9OriginalNativeBlockFockOrderedListUnitarityProbe

/-!
S1V52L9E5F11 — STAGED / UNQUALIFIED; do NOT run a strict gate
until source-exact F10 ordered-product identification qualifies.

This targets the actual single element
  originalNativeSixteenSpinHom g : spinGroup source48Quadratic
and its actual original Fermion-2 Hilbert operator image.
F9 independently proves two-sided Hilbert-adjoint unitarity of
all ordered native per-block Fock operator products, while F10
must identify this operator list product with the image of
the original genuine native sixteen-block Spin48 element.

NO claim about full Spin48 unitarity beyond this gauge-image
subgroup, original physical gauge operator equality, original
Hilbert physical-charge domains, spectral gap, or BFSS truth.
-/

set_option autoImplicit false
set_option maxHeartbeats 360000

namespace FCP.BFSSS1V52L9E5F11
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L7C7
open FCP.BFSSS1V52L8E
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5F9
open FCP.BFSSS1V52L9E5F10

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- Two-sided Hilbert-adjoint LEFT inverse of the ACTUAL
original sixteen-block native Spin48 gauge image in the
ACTUAL original Fermion2 Fock operator representation. -/
theorem originalNativeSixteenSpin48Fock_adjoint_mul
    (g : GaugeGroup 2) :
    star (originalFockCliffordAlgHom
      (((originalNativeSixteenSpinHom g : spinGroup Q) : C))) *
      originalFockCliffordAlgHom
        (((originalNativeSixteenSpinHom g : spinGroup Q) : C)) =
      (1 : FockOp) := by
  have h := originalNativeBlockFockOrderedProd_adjoint_mul
    g originalNativeSixteenSpinBlocks
  change
    star ((originalNativeSixteenSpinBlocks.map
      (fun α => originalFockCliffordAlgHom
        (((originalNativeGaugeSpinHom α g : spinGroup Q) : C)))).prod) *
      (originalNativeSixteenSpinBlocks.map
        (fun α => originalFockCliffordAlgHom
          (((originalNativeGaugeSpinHom α g : spinGroup Q) : C)))).prod =
      (1 : FockOp) at h
  rw [originalNativeSixteenSpinFock_eq_orderedProd]
  exact h

/-- The independent Hilbert-adjoint RIGHT inverse for the
very same original native sixteen-block Spin48 image. -/
theorem originalNativeSixteenSpin48Fock_mul_adjoint
    (g : GaugeGroup 2) :
    originalFockCliffordAlgHom
      (((originalNativeSixteenSpinHom g : spinGroup Q) : C)) *
      star (originalFockCliffordAlgHom
        (((originalNativeSixteenSpinHom g : spinGroup Q) : C))) =
      (1 : FockOp) := by
  have h := originalNativeBlockFockOrderedProd_mul_adjoint
    g originalNativeSixteenSpinBlocks
  change
    (originalNativeSixteenSpinBlocks.map
      (fun α => originalFockCliffordAlgHom
        (((originalNativeGaugeSpinHom α g : spinGroup Q) : C)))).prod *
      star ((originalNativeSixteenSpinBlocks.map
        (fun α => originalFockCliffordAlgHom
          (((originalNativeGaugeSpinHom α g : spinGroup Q) : C)))).prod) =
      (1 : FockOp) at h
  rw [originalNativeSixteenSpinFock_eq_orderedProd]
  exact h

#print axioms originalNativeSixteenSpin48Fock_adjoint_mul
#print axioms originalNativeSixteenSpin48Fock_mul_adjoint

end
end FCP.BFSSS1V52L9E5F11
