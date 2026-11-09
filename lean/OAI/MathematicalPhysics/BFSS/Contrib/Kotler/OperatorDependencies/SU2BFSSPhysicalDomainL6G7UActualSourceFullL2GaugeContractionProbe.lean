import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7TOriginalFullColorLieGaussIdentityProbe

/-!
L6G7U — norm-bounded ACTUAL BFSS FullL2 gauge transformation.

The original GaugeCore physicalSpace uses the source bosonPullback and
fiberAction; the source physical projector's integrand instead combines
the fermionic action at g and bosonic pullback at g⁻¹.

This module uses the literal six-field pairedGaugeData, its original
GaugeCore maps and the exact pinned Lp bounded composition theorems
to qualify a norm-at-most-one complex-linear FullL2 endomorphism
for EVERY genuine SU(2) element.

This bounds finite group transformations, NOT their strong derivative,
a (closed) Gauss generator, or BFSS spectral theory. Existing D2B6
prospective source is not silently assumed qualified or imported.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace FCP.BFSSSU2PhysicalDomainL6G7U
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG4J
open MeasureTheory

/-- Literal original fermionic gauge fiber action is nonexpansive on
the exact source BFSS Hilbert type FullL2 2. -/
theorem originalSourceFermionFiberAction_norm_le
    (g : GaugeGroup 2) (v : FullL2 2) :
    ‖pairedGaugeData.fiberAction g v‖ ≤ ‖v‖ := by
  let L : Fermion 2 →L[ℂ] Fermion 2 :=
    (pairedGaugeData.fermion g).toContinuousLinearEquiv.toContinuousLinearMap
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro a
    change ‖pairedGaugeData.fermion g a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using
      (pairedGaugeData.fermion g).norm_map a |>.le
  have hv : ‖L.compLp v‖ ≤ ‖L‖ * ‖v‖ := L.norm_compLp_le v
  have h : ‖L.compLp v‖ ≤ ‖v‖ := by
    calc
      _ ≤ ‖L‖ * ‖v‖ := hv
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg v)
      _ = ‖v‖ := one_mul _
  change ‖L.compLp v‖ ≤ ‖v‖
  exact h

/-- Bosonic source pullback is exactly an L² isometry, because
the ORIGINAL GaugeData boson homomorphism takes values in
real-linear Euclidean isometries with invariant volume. -/
theorem originalSourceBosonPullback_norm
    (g : GaugeGroup 2) (v : FullL2 2) :
    ‖pairedGaugeData.bosonPullback g v‖ = ‖v‖ := by
  change ‖(Lp.compMeasurePreservingₗᵢ ℂ
    (pairedGaugeData.boson g)
    (pairedGaugeData.boson g).measurePreserving) v‖ = ‖v‖
  exact (Lp.compMeasurePreservingₗᵢ ℂ
    (pairedGaugeData.boson g)
    (pairedGaugeData.boson g).measurePreserving).norm_map v

/-- Genuine original FullL2 source gauge pair with the inverse
bosonic action: U(g) v = fiberAction g (bosonPullback g⁻¹ v).
This is the ORIGINAL Haar/invariant-core gauge convention. -/
noncomputable def actualOriginalFullL2GaugePairCLM
    (g : GaugeGroup 2) : FullL2 2 →L[ℂ] FullL2 2 :=
  (((pairedGaugeData.fermion g).toContinuousLinearEquiv.toContinuousLinearMap).compLpL
    2 (volume : Measure (Boson 2))).comp
    ((Lp.compMeasurePreservingₗᵢ ℂ (pairedGaugeData.boson g⁻¹)
      (pairedGaugeData.boson g⁻¹).measurePreserving).toContinuousLinearMap)

/-- Equality to the real pinned source transformations is
definitionally exact; no replacement gauge actions are introduced. -/
theorem actualOriginalFullL2GaugePairCLM_apply
    (g : GaugeGroup 2) (v : FullL2 2) :
    actualOriginalFullL2GaugePairCLM g v =
      pairedGaugeData.fiberAction g (pairedGaugeData.bosonPullback g⁻¹ v) := rfl

/-- Uniform nonexpansiveness across all genuine source SU(2)
group elements. Key finite-operator bound for future attempts
at strong continuity / infinitesimal generator domain. -/
theorem actualOriginalFullL2GaugePairCLM_norm_le_one
    (g : GaugeGroup 2) :
    ‖actualOriginalFullL2GaugePairCLM g‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  change ‖pairedGaugeData.fiberAction g
    (pairedGaugeData.bosonPullback g⁻¹ v)‖ ≤ 1 * ‖v‖
  simpa only [one_mul, originalSourceBosonPullback_norm] using
    originalSourceFermionFiberAction_norm_le g
      (pairedGaugeData.bosonPullback g⁻¹ v)

#print axioms originalSourceFermionFiberAction_norm_le
#print axioms originalSourceBosonPullback_norm
#print axioms actualOriginalFullL2GaugePairCLM
#print axioms actualOriginalFullL2GaugePairCLM_apply
#print axioms actualOriginalFullL2GaugePairCLM_norm_le_one
#check @actualOriginalFullL2GaugePairCLM_norm_le_one

end
end FCP.BFSSSU2PhysicalDomainL6G7U
