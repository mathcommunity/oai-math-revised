import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F9OriginalNativeBlockFockOrderedListUnitarityProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L8EOriginalOrderedSixteenNativeSU2Spin48HomProbe

/-!
S1V52L9E5F10 — STAGED / UNQUALIFIED, NO roots without strict CI.

SOURCE-EXACT identification:
the genuine original CliffordAlgebra->Fermion2 continuous-operator
algebra hom maps the genuine Spin48 ordered List.prod of the
original native per-block homs to the original Fock ordered product
of their images, preserving the literal (noncommutative) list order.
Then specialize to the genuine original L8E sixteen-block native
Spin48 hom. No surrogates, false commutativity, extra axioms,
global Clifford star preservation, physical gauge operator
identification, or BFSS spectral assertions.

Only this product-IDENTIFICATION is targeted here; transfer
of F9 accepted actual adjoint-unitarity to the sixteen-block
Spin48 element is a subsequent gate.
-/

set_option autoImplicit false
set_option maxHeartbeats 360000

namespace FCP.BFSSS1V52L9E5F10
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L7C7
open FCP.BFSSS1V52L8E
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5F9

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- Exact original native Spin48 source-list product maps to the
exact original complex-linear Fock-operator list product in
unchanged (and potentially noncommuting) source list order. -/
theorem originalNativeSpinBlockList_fock_map_prod
    (g : GaugeGroup 2) (xs : List RealSpinBlock) :
    originalFockCliffordAlgHom
      ((((xs.map (fun α => originalNativeGaugeSpinHom α g)).prod :
        spinGroup Q) : C)) =
      (xs.map (fun α =>
        originalFockCliffordAlgHom
          (((originalNativeGaugeSpinHom α g : spinGroup Q) : C)))).prod := by
  induction xs with
  | nil =>
      change originalFockCliffordAlgHom (1 : C) = (1 : FockOp)
      exact map_one originalFockCliffordAlgHom
  | cons α xs ih =>
      change originalFockCliffordAlgHom
          (((originalNativeGaugeSpinHom α g *
              (xs.map (fun β => originalNativeGaugeSpinHom β g)).prod :
                spinGroup Q) : C)) =
        originalFockCliffordAlgHom
          (((originalNativeGaugeSpinHom α g : spinGroup Q) : C)) *
          (xs.map (fun β =>
            originalFockCliffordAlgHom
              (((originalNativeGaugeSpinHom β g : spinGroup Q) : C)))).prod
      calc
        originalFockCliffordAlgHom
            (((originalNativeGaugeSpinHom α g *
                (xs.map (fun β => originalNativeGaugeSpinHom β g)).prod :
                  spinGroup Q) : C)) =
          originalFockCliffordAlgHom
            (((originalNativeGaugeSpinHom α g : spinGroup Q) : C) *
              (((xs.map (fun β => originalNativeGaugeSpinHom β g)).prod :
                spinGroup Q) : C)) := by
                  rfl
        _ = originalFockCliffordAlgHom
              (((originalNativeGaugeSpinHom α g : spinGroup Q) : C)) *
            originalFockCliffordAlgHom
              ((((xs.map (fun β => originalNativeGaugeSpinHom β g)).prod :
                spinGroup Q) : C)) := by
                  rw [map_mul]
        _ = originalFockCliffordAlgHom
              (((originalNativeGaugeSpinHom α g : spinGroup Q) : C)) *
            (xs.map (fun β =>
              originalFockCliffordAlgHom
                (((originalNativeGaugeSpinHom β g : spinGroup Q) : C)))).prod := by
                  rw [ih]

/-- Exact Fock image of the SINGLE GENUINE original native
16-block Spin48 group element, not a new list-based group
or unverified gauge implementation. -/
theorem originalNativeSixteenSpinFock_eq_orderedProd
    (g : GaugeGroup 2) :
    originalFockCliffordAlgHom
      (((originalNativeSixteenSpinHom g : spinGroup Q) : C)) =
        (originalNativeSixteenSpinBlocks.map
          (fun α => originalFockCliffordAlgHom
            (((originalNativeGaugeSpinHom α g : spinGroup Q) : C)))).prod := by
  rw [originalNativeSixteenSpinHom_apply]
  exact originalNativeSpinBlockList_fock_map_prod
    g originalNativeSixteenSpinBlocks

#print axioms originalNativeSpinBlockList_fock_map_prod
#print axioms originalNativeSixteenSpinFock_eq_orderedProd

end
end FCP.BFSSS1V52L9E5F10
