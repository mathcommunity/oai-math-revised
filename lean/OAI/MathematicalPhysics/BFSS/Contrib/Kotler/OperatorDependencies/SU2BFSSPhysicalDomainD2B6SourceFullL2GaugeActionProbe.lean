import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B5SourceProjectionAlgebraProbe

/-!
# BFSS SU2 D2B6 — bounded gauge transformations on the ORIGINAL full L²

PROSPECTIVE / UNCOMPILED until pinned dedicated CI passes.

Use the actual source `FullL2 2`, `G.bosonPullback`, `G.fiberAction`,
and the actual original SU2 gauge actions. The goal is to construct
and bound the original full-Hilbert-space GAUGE TRANSFORMATION,
not to postulate or assume a full L² Haar-average projection.

The accepted D2B5 source SmoothCore Haar map is complex-linear and
idempotent, but its full-L² bounded extension is NOT yet proved.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B6
noncomputable section
open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2B5
open MeasureTheory

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- The ORIGINAL fermionic fiber gauge action is nonexpansive on
the exact BFSS full Hilbert space. This uses the pinned Mathlib
norm bound for applying the true source complex-linear isometry
to L² functions, not a new fermion representation. -/
theorem sourceFermionFiberAction_norm_le
    (g : GaugeGroup 2) (v : FullL2 2) :
    ‖G.fiberAction g v‖ ≤ ‖v‖ := by
  change ‖((G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap).compLp v‖ ≤ ‖v‖
  have h :=
    ((G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap).norm_compLp_le v
  simpa using h

/-- The source fiber action is a genuinely continuous function of
its Hilbert vector for every fixed SU2 group element. -/
theorem sourceFermionFiberAction_continuous (g : GaugeGroup 2) :
    Continuous (G.fiberAction g : FullL2 2 → FullL2 2) := by
  exact
    ((G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
      2 (volume : Measure (Boson 2))).continuous

/-- Combine BOTH original bosonic and fermionic L² gauge actions,
using only their existing source-map definitions. The inverse
boson pullback implements the same convention as source Haar
averaging: `f(x) ↦ G.fermion g (f (G.boson g⁻¹ x))`. -/
theorem sourceFullGaugePair_norm_le
    (g : GaugeGroup 2) (v : FullL2 2) :
    ‖G.fiberAction g (G.bosonPullback g⁻¹ v)‖ ≤ ‖v‖ := by
  have h := sourceFermionFiberAction_norm_le M G g
    (G.bosonPullback g⁻¹ v)
  rw [sourceBosonPullback_norm M G g⁻¹ v] at h
  exact h

/-- A continuous complex-linear operator on the genuine BFSS
FullL2 space for each true SU2 gauge element. The component
operators are the same ones defining source `G.physicalSpace`. -/
noncomputable def sourceFullGaugePairCLM
    (g : GaugeGroup 2) : FullL2 2 →L[ℂ] FullL2 2 :=
  (((G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap).compLpL
    2 (volume : Measure (Boson 2))).comp
    ((Lp.compMeasurePreservingₗᵢ ℂ (G.boson g⁻¹)
      (G.boson g⁻¹).measurePreserving).toContinuousLinearMap)

/-- Identify the newly PACKAGED bounded operator with the genuine
original BFSS gauge pair, no proxy or replacement action. -/
theorem sourceFullGaugePairCLM_apply
    (g : GaugeGroup 2) (v : FullL2 2) :
    sourceFullGaugePairCLM M G g v =
      G.fiberAction g (G.bosonPullback g⁻¹ v) := rfl

/-- Exact source SU2 L² gauge transformations have operator norm
at most one. This is the first full Hilbert-space contraction
step and DOES NOT assert Haar-average contractivity. -/
theorem sourceFullGaugePairCLM_norm_le_one
    (g : GaugeGroup 2) :
    ‖sourceFullGaugePairCLM M G g‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  change ‖G.fiberAction g (G.bosonPullback g⁻¹ v)‖ ≤ 1 * ‖v‖
  simpa only [one_mul] using sourceFullGaugePair_norm_le M G g v

#print axioms sourceFermionFiberAction_norm_le
#print axioms sourceFermionFiberAction_continuous
#print axioms sourceFullGaugePair_norm_le
#print axioms sourceFullGaugePairCLM_apply
#print axioms sourceFullGaugePairCLM_norm_le_one

end
end FCP.BFSSSU2PhysicalDomainD2B6
