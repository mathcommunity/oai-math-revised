import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B8CBosonStrongContinuityProbe

/-!
# BFSS SU2 D2B9A — existence and contraction of genuine full-L2 Haar average

PROSPECTIVE / UNCOMPILED until exact pinned CI accepts all axiom reports.

D2B8C proved unconditional strong continuity of every original
FullL2 SU2 gauge orbit. Hence that orbit is Bochner-integrable against
the ORIGINAL normalized source Haar measure on the compact GaugeGroup 2.

This leaf defines the genuine source Hilbert-space Haar integral,
proves its pointwise L2 contractive bound using D2B7 isometries, and
shows it fixes the exact original physical Hilbert vectors.

This does NOT prove full-Hilbert Haar projection invariance,
idempotence, linear-map packaging or compatibility with the source
SmoothCore Haar average; those remain separately OPEN.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B9A
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open OAI.Laughlin.Rotation
open FCP.BFSSSU2PhysicalDomainD2B1
open FCP.BFSSSU2PhysicalDomainD2B6
open FCP.BFSSSU2PhysicalDomainD2B7
open FCP.BFSSSU2PhysicalDomainD2B8C
open MeasureTheory

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- The actual FullL2 gauge orbit is Bochner-integrable for the
existing normalized SU2 Haar measure, unconditionally. -/
theorem sourceFullHaarIntegrand_integrable (v : FullL2 2) :
    Integrable (fun g : GaugeGroup 2 =>
      sourceFullGaugePairCLM M G g v) sourceHaar :=
  (sourceFullGaugePair_strongContinuous M G v).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The genuine source full-Hilbert-space SU2 Haar integral,
not an assumed or surrogate operator. -/
noncomputable def sourceFullHaarAverage (v : FullL2 2) : FullL2 2 :=
  ∫ g : GaugeGroup 2, sourceFullGaugePairCLM M G g v ∂sourceHaar

/-- Source full-L2 Haar averaging is contractive ON VECTORS.
The only analytic estimates are norm-of-integral and D2B7's
true-source gauge isometry; probability mass is source Haar's 1. -/
theorem sourceFullHaarAverage_norm_le (v : FullL2 2) :
    ‖sourceFullHaarAverage M G v‖ ≤ ‖v‖ := by
  calc
    ‖sourceFullHaarAverage M G v‖ =
        ‖∫ g : GaugeGroup 2,
          sourceFullGaugePairCLM M G g v ∂sourceHaar‖ := rfl
    _ ≤ ∫ g : GaugeGroup 2, ‖sourceFullGaugePairCLM M G g v‖ ∂sourceHaar :=
      norm_integral_le_integral_norm _
    _ = ‖v‖ := by simp [sourceFullGaugePairCLM_norm_map]

/-- The source full-L2 Haar average fixes all genuinely physical
Hilbert states, because all original SU2 gauge operators fix them. -/
theorem sourceFullHaarAverage_fixed_physical
    (v : FullL2 2) (hv : v ∈ G.physicalSpace) :
    sourceFullHaarAverage M G v = v := by
  unfold sourceFullHaarAverage
  have hfixed (g : GaugeGroup 2) :
      sourceFullGaugePairCLM M G g v = v :=
    sourceFullGaugePairCLM_fixed_physical M G g v hv
  simp [hfixed]

#print axioms sourceFullHaarIntegrand_integrable
#print axioms sourceFullHaarAverage_norm_le
#print axioms sourceFullHaarAverage_fixed_physical

end
end FCP.BFSSSU2PhysicalDomainD2B9A
