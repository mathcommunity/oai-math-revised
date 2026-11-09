import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B9AFullL2HaarExistenceBoundProbe

/-!
# BFSS SU2 D2B9B — genuine source full-Hilbert Haar averaging is a contraction CLM

PROSPECTIVE / UNCOMPILED until the exact pinned CI gate passes.

D2B9A established existence of the original GaugeData SU2 FullL2 Haar integral
and an L2 contraction estimate, with the genuine pinned Haar measure.
This leaf proves complex linearity and packages the same integral into the
original FullL2 2 →L[ℂ] FullL2 2, without introducing any new operator action.

Do not call this a projection yet. Gauge invariance, idempotence, and
compatibility with the original smooth-core average remain OPEN.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B9B
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2B6
open FCP.BFSSSU2PhysicalDomainD2B9A
open MeasureTheory

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- Complex additivity of the TRUE source FullL2 Haar integral. -/
theorem sourceFullHaarAverage_add (v w : FullL2 2) :
    sourceFullHaarAverage M G (v + w) =
      sourceFullHaarAverage M G v + sourceFullHaarAverage M G w := by
  change (∫ g : GaugeGroup 2, sourceFullGaugePairCLM M G g (v + w) ∂
    OAI.Laughlin.Rotation.sourceHaar) =
      (∫ g : GaugeGroup 2, sourceFullGaugePairCLM M G g v ∂
        OAI.Laughlin.Rotation.sourceHaar) +
      (∫ g : GaugeGroup 2, sourceFullGaugePairCLM M G g w ∂
        OAI.Laughlin.Rotation.sourceHaar)
  calc
    _ = ∫ g : GaugeGroup 2,
      (sourceFullGaugePairCLM M G g v +
        sourceFullGaugePairCLM M G g w) ∂
          OAI.Laughlin.Rotation.sourceHaar := by
            apply integral_congr_ae
            filter_upwards [] with g
            exact map_add (sourceFullGaugePairCLM M G g) v w
    _ = _ := integral_add
      (sourceFullHaarIntegrand_integrable M G v)
      (sourceFullHaarIntegrand_integrable M G w)

/-- Complex scalar linearity of the TRUE source FullL2 Haar integral. -/
theorem sourceFullHaarAverage_smul (c : ℂ) (v : FullL2 2) :
    sourceFullHaarAverage M G (c • v) =
      c • sourceFullHaarAverage M G v := by
  change (∫ g : GaugeGroup 2, sourceFullGaugePairCLM M G g (c • v) ∂
    OAI.Laughlin.Rotation.sourceHaar) =
      c • (∫ g : GaugeGroup 2, sourceFullGaugePairCLM M G g v ∂
        OAI.Laughlin.Rotation.sourceHaar)
  calc
    _ = ∫ g : GaugeGroup 2, c • (sourceFullGaugePairCLM M G g v) ∂
        OAI.Laughlin.Rotation.sourceHaar := by
          apply integral_congr_ae
          filter_upwards [] with g
          exact map_smul (sourceFullGaugePairCLM M G g) c v
    _ = _ := integral_smul c _

/-- Original full-L² SU2 Haar integration packaged as a complex linear map. -/
noncomputable def sourceFullHaarAverageLinear :
    FullL2 2 →ₗ[ℂ] FullL2 2 where
  toFun := sourceFullHaarAverage M G
  map_add' v w := sourceFullHaarAverage_add M G v w
  map_smul' c v := sourceFullHaarAverage_smul M G c v

/-- The SAME true-source Haar integral as a bounded complex-linear map.
Its norm bound follows directly from the D2B9A source estimate. -/
noncomputable def sourceFullHaarAverageCLM :
    FullL2 2 →L[ℂ] FullL2 2 :=
  (sourceFullHaarAverageLinear M G).mkContinuous 1 (by
    intro v
    change ‖sourceFullHaarAverage M G v‖ ≤ 1 * ‖v‖
    simpa only [one_mul] using sourceFullHaarAverage_norm_le M G v)

/-- This new CLM acts by the EXACT D2B9A Bochner integral. -/
theorem sourceFullHaarAverageCLM_apply (v : FullL2 2) :
    sourceFullHaarAverageCLM M G v = sourceFullHaarAverage M G v := rfl

/-- Full-Hilbert source Haar complex-linear operator has norm ≤ 1. -/
theorem sourceFullHaarAverageCLM_norm_le_one :
    ‖sourceFullHaarAverageCLM M G‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  change ‖sourceFullHaarAverage M G v‖ ≤ 1 * ‖v‖
  simpa only [one_mul] using sourceFullHaarAverage_norm_le M G v

/-- Every original physical Hilbert vector is fixed by the
actual source Haar continuous-linear operator. -/
theorem sourceFullHaarAverageCLM_fixed_physical
    (v : FullL2 2) (hv : v ∈ G.physicalSpace) :
    sourceFullHaarAverageCLM M G v = v := by
  rw [sourceFullHaarAverageCLM_apply]
  exact sourceFullHaarAverage_fixed_physical M G v hv

#print axioms sourceFullHaarAverage_add
#print axioms sourceFullHaarAverage_smul
#print axioms sourceFullHaarAverageCLM_apply
#print axioms sourceFullHaarAverageCLM_norm_le_one
#print axioms sourceFullHaarAverageCLM_fixed_physical

end
end FCP.BFSSSU2PhysicalDomainD2B9B
