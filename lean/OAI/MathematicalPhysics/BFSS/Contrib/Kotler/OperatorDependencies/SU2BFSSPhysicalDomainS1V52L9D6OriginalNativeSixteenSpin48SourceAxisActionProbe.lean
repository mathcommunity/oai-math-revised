import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9D5OriginalNativeOrderedSpin48BlockListVectorActionProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L8EOriginalOrderedSixteenNativeSU2Spin48HomProbe

/-!
S1V52L9D6 — STAGED, UNQUALIFIED original exact 16-block Spin(48)
homomorphism 48-real Majorana source-axis action, with original
native SU2 BFSS color-adjoint coefficients.

The actual original 16-block list is List.finRange 16 mapped by
the original finProdFinEquiv inverse, and is Nodup per accepted
L8E. The upstream L9D5 induction over genuine noncommutative
Spin48 block products remains a candidate until independently
qualified; do not compile/accept this specialization before L9D5.

Matching with actual original paired Fock sourceRealMajoranaMatrix
and proving the precise global sourceSpin48CoversActualGauge
predicate are separate unproved obligations, even if this source
axis theorem subsequently becomes kernel-qualified.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000

namespace FCP.BFSSS1V52L9D6
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L8E
open FCP.BFSSS1V52L9D5
open FCP.BFSSSU2GaugeG3A

/-- All sixteen ORIGINAL source RealSpinBlock labels occur in the
genuine L8E native Spin48 product list. -/
theorem originalNativeSixteenSpinBlocks_mem
    (α : RealSpinBlock) :
    α ∈ originalNativeSixteenSpinBlocks := by
  unfold originalNativeSixteenSpinBlocks
  apply List.mem_map.mpr
  refine ⟨(finProdFinEquiv : RealSpinBlock ≃ Fin 16) α,
    List.mem_finRange _, ?_⟩
  simp

/-- The ordered genuine original native SU2 → Spin(48) lift
acts on each actual source 48-real Majorana coordinate exactly
by the original BFSS native SU2 color-adjoint matrix. -/
theorem originalNativeSixteenSpinHom_sourceAxis_action
    (g : GaugeGroup 2) (α : RealSpinBlock) (A : Fin 3) :
    FCP.BFSSS1V31.sourceSpin48VectorAction
      (originalNativeSixteenSpinHom g)
      (sourceBlockColorAxis α A) =
      ∑ B : Fin 3,
        (adjointColorMatrix g B A) • sourceBlockColorAxis α B := by
  rw [originalNativeSixteenSpinHom_apply]
  change FCP.BFSSS1V31.sourceSpin48VectorAction
      (FCP.BFSSS1V52L8D.originalNativeBlockSpinProd
        originalNativeSixteenSpinBlocks g)
      (sourceBlockColorAxis α A) =
      ∑ B : Fin 3,
        (adjointColorMatrix g B A) • sourceBlockColorAxis α B
  exact originalNativeBlockSpinProd_member_action α g A
    originalNativeSixteenSpinBlocks
    originalNativeSixteenSpinBlocks_nodup
    (originalNativeSixteenSpinBlocks_mem α)

#print axioms originalNativeSixteenSpinBlocks_mem
#print axioms originalNativeSixteenSpinHom_sourceAxis_action

end
end FCP.BFSSS1V52L9D6
