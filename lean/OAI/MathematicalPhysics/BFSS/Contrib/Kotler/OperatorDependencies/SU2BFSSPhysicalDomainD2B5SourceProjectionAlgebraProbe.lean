import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B4SourceSmoothInvariantCoreProbe

/-!
# BFSS SU2 D2B5 — exact-source smooth Haar projection algebra

PROSPECTIVE / UNCOMPILED until the pinned GitHub Actions gate passes.

D2B4 has produced the ORIGINAL source SmoothCore 2-valued Haar average,
and proved its exact original invariant-core membership and fixedness.
This next leaf tests the algebra of the SAME operator and a genuine
L2 norm identity for the source bosonic action.

This does NOT claim bounded extension or contraction of the average
on the full original L2 Hilbert space, nor physical-core L2 density.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B5
noncomputable section
open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open OAI.Laughlin.Rotation
open FCP.BFSSSU2PhysicalDomainD2B1
open FCP.BFSSSU2PhysicalDomainD2B4
open MeasureTheory
open scoped Topology ContDiff

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- Linearity of the true source Haar integral under addition,
as equality of ORIGINAL bundled BFSS SmoothCore test functions. -/
theorem sourceHaarAverageCore_add (f h : SmoothCore 2) :
    sourceHaarAverageCore M G (f + h) =
      sourceHaarAverageCore M G f + sourceHaarAverageCore M G h := by
  apply TestFunction.ext
  intro x
  change (∫ g : GaugeGroup 2,
      G.fermion g ((f + h) (G.boson g⁻¹ x)) ∂sourceHaar) =
    (∫ g : GaugeGroup 2,
      G.fermion g (f (G.boson g⁻¹ x)) ∂sourceHaar) +
    (∫ g : GaugeGroup 2,
      G.fermion g (h (G.boson g⁻¹ x)) ∂sourceHaar)
  calc
    _ = ∫ g : GaugeGroup 2,
        (G.fermion g (f (G.boson g⁻¹ x)) +
          G.fermion g (h (G.boson g⁻¹ x))) ∂sourceHaar := by
            apply integral_congr_ae
            filter_upwards [] with g
            simp only [add_apply, map_add]
    _ = _ := integral_add
      (sourceHaarIntegrand_integrable M G f x)
      (sourceHaarIntegrand_integrable M G h x)

/-- Genuine complex-scalar compatibility of source Haar averaging. -/
theorem sourceHaarAverageCore_smul (c : ℂ) (f : SmoothCore 2) :
    sourceHaarAverageCore M G (c • f) =
      c • sourceHaarAverageCore M G f := by
  apply TestFunction.ext
  intro x
  change (∫ g : GaugeGroup 2,
      G.fermion g ((c • f) (G.boson g⁻¹ x)) ∂sourceHaar) =
    c • (∫ g : GaugeGroup 2,
      G.fermion g (f (G.boson g⁻¹ x)) ∂sourceHaar)
  calc
    _ = ∫ g : GaugeGroup 2,
        c • (G.fermion g (f (G.boson g⁻¹ x))) ∂sourceHaar := by
            apply integral_congr_ae
            filter_upwards [] with g
            simp only [smul_apply, map_smul]
    _ = _ := integral_smul c _

/-- The exact original-source Haar operator as a complex-linear
map ON the original SmoothCore 2, without any new gauge assumption. -/
noncomputable def sourceHaarAverageCore_linear :
    SmoothCore 2 →ₗ[ℂ] SmoothCore 2 where
  toFun := sourceHaarAverageCore M G
  map_add' f h := sourceHaarAverageCore_add M G f h
  map_smul' c f := sourceHaarAverageCore_smul M G c f

theorem sourceHaarAverageCore_linear_apply (f : SmoothCore 2) :
    sourceHaarAverageCore_linear M G f =
      sourceHaarAverageCore M G f := rfl

/-- This is an ACTUAL idempotent projection on the source smooth
test functions, since every averaged function lies in the source
invariantCore and averaging fixes all such functions. -/
theorem sourceHaarAverageCore_idempotent (f : SmoothCore 2) :
    sourceHaarAverageCore M G (sourceHaarAverageCore M G f) =
      sourceHaarAverageCore M G f := by
  let a : G.invariantCore :=
    ⟨sourceHaarAverageCore M G f,
      sourceHaarAverageCore_mem_invariantCore M G f⟩
  exact sourceHaarAverageCore_fixed M G a

/-- Original source bosonPullback is isometric ON THE FULL BFSS L2
Hilbert space. This uses the original measure-preserving boson
linear isometry, not an auxiliary group representation. -/
theorem sourceBosonPullback_norm (g : GaugeGroup 2) (v : FullL2 2) :
    ‖G.bosonPullback g v‖ = ‖v‖ := by
  change ‖(Lp.compMeasurePreservingₗᵢ ℂ (G.boson g)
    (G.boson g).measurePreserving) v‖ = ‖v‖
  exact (Lp.compMeasurePreservingₗᵢ ℂ (G.boson g)
    (G.boson g).measurePreserving).norm_map v

#print axioms sourceHaarAverageCore_add
#print axioms sourceHaarAverageCore_smul
#print axioms sourceHaarAverageCore_linear_apply
#print axioms sourceHaarAverageCore_idempotent
#print axioms sourceBosonPullback_norm

end
end FCP.BFSSSU2PhysicalDomainD2B5
