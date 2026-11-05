import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L8DOriginalNodupNativeBlockSpin48ListHomProbe

/-!
S1V52-L8E — STAGED, UNQUALIFIED original native SU2→true
source Spin48 sixteen-block ordered product homomorphism.

The ordered 16 source RealSpinBlock indices use the previously
accepted S1V9/S1V15 SAME canonical
`(finProdFinEquiv : RealSpinBlock ≃ Fin 16).symm` and
`List.finRange 16` order. The exact pinned 48-real
source color-spin Clifford representation and L7C7 per-block
original native SU2 Spin48 homomorphisms are preserved.

L8C arbitrary genuine Spin48 cross-block image commutation and
L8D nodup-list product hom still REQUIRE their own STRICT
qualification; this L8E file is only a successor proposal.
The original physical G1A pairedLabelEquiv and original Fock
matrix order bridge, global spin action and continuity remain
separate unproved obligations even after L8E qualification.
-/
set_option autoImplicit false
set_option maxHeartbeats 380000

namespace FCP.BFSSS1V52L8E
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L7C7
open FCP.BFSSS1V52L8D

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Exactly the accepted source finite 16-block canonical order. -/
noncomputable def originalNativeSixteenSpinBlocks : List RealSpinBlock :=
  (List.finRange 16).map
    (finProdFinEquiv : RealSpinBlock ≃ Fin 16).symm

/-- The list contains each original source real-spin block exactly
once; no group-level commutative assumption is smuggled in. -/
theorem originalNativeSixteenSpinBlocks_nodup :
    originalNativeSixteenSpinBlocks.Nodup := by
  unfold originalNativeSixteenSpinBlocks
  exact (List.nodup_finRange 16).map
    (finProdFinEquiv : RealSpinBlock ≃ Fin 16).symm.injective

theorem originalNativeSixteenSpinBlocks_length :
    originalNativeSixteenSpinBlocks.length = 16 := by
  simp [originalNativeSixteenSpinBlocks]

/-- ACTUAL original native GaugeGroup2 to true Spin48 monoid hom,
an ordered product of precisely 16 original-source block homs.
NO hypothesized multiplicativity: it is supplied by L8D. -/
noncomputable def originalNativeSixteenSpinHom :
    GaugeGroup 2 →* spinGroup Q :=
  originalNativeBlockSpinHom_of_nodup
    originalNativeSixteenSpinBlocks originalNativeSixteenSpinBlocks_nodup

/-- Its exact underlying source Spin48 element is the specified
noncommutative ordered product, not a Finset.prod or surrogate
commuting spin group. -/
theorem originalNativeSixteenSpinHom_apply (g : GaugeGroup 2) :
    originalNativeSixteenSpinHom g =
      (originalNativeSixteenSpinBlocks.map
        (fun α => originalNativeGaugeSpinHom α g)).prod := rfl

#print axioms originalNativeSixteenSpinBlocks
#print axioms originalNativeSixteenSpinBlocks_nodup
#print axioms originalNativeSixteenSpinBlocks_length
#print axioms originalNativeSixteenSpinHom
#print axioms originalNativeSixteenSpinHom_apply
end
end FCP.BFSSS1V52L8E
