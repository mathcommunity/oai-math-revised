import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B8BFermionContinuousReductionProbe
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# BFSS SU2 D2B8C — unconditional strong continuity of genuine FullL2 gauge action

PROSPECTIVE / UNCOMPILED until the exact pinned Lean CI gate passes.

Use the ORIGINAL source GaugeData.boson group homomorphism, its
actual joint continuity and measure-preserving linear isometries,
and the pinned Mathlib Lp composition-continuity theorem.

D2B8B has already established true-source fermion L2
parameter continuity and conditional full gauge strong continuity.
This leaf discharges that precise bosonic L2 pullback hypothesis.

No substitute gauge action, added GaugeData regularity assumption,
new axiom, or claimed full-Hilbert Haar projection is admitted.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B8C
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2B6
open FCP.BFSSSU2PhysicalDomainD2B8B
open MeasureTheory

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- Package the original gauge bosonic inverse isometry as a
continuous map; this changes neither the bosonic action nor the
underlying BFSS configuration space. -/
private def sourceBosonContinuousMap (g : GaugeGroup 2) :
    C(Boson 2, Boson 2) :=
  ⟨fun x => G.boson g⁻¹ x, (G.boson g⁻¹).continuous⟩

/-- The original source gauge bosonic inverse action varies
continuously in the compact-open topology of continuous maps,
following from the actual source joint action continuity. -/
theorem sourceBosonContinuousMap_parameter_continuous :
    Continuous (sourceBosonContinuousMap M G) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : GaugeGroup 2 × Boson 2 =>
    G.boson p.1⁻¹ p.2)
  exact G.boson_continuous.comp
    ((continuous_inv.comp continuous_fst).prodMk continuous_snd)

/-- Strong SU2 continuity of the ORIGINAL bosonic pullback on every
original BFSS FullL2 vector, with no smooth-core qualification.
Use precisely the pinned Lp theorem for parameter-continuous,
volume-measure-preserving maps and p=2. -/
theorem sourceBosonPullback_strongContinuous (v : FullL2 2) :
    Continuous (fun g : GaugeGroup 2 =>
      G.bosonPullback g⁻¹ v) := by
  have hmaps := sourceBosonContinuousMap_parameter_continuous M G
  have hmp (g : GaugeGroup 2) :
      MeasurePreserving (sourceBosonContinuousMap M G g)
        (volume : Measure (Boson 2))
        (volume : Measure (Boson 2)) :=
    (G.boson g⁻¹).measurePreserving
  have h := (continuous_const : Continuous (fun _ : GaugeGroup 2 => v))
    |>.compMeasurePreservingLp hmaps hmp (by norm_num)
  exact h

/-- The FULL original combined source SU2 gauge orbit map is strongly
continuous on every BFSS FullL2 vector. This removes D2B8B's
explicit bosonic hypothesis using the original source measure action. -/
theorem sourceFullGaugePair_strongContinuous (v : FullL2 2) :
    Continuous (fun g : GaugeGroup 2 =>
      sourceFullGaugePairCLM M G g v) :=
  sourceFullGaugePair_strongContinuous_of_boson M G
    (sourceBosonPullback_strongContinuous M G) v

#print axioms sourceBosonContinuousMap_parameter_continuous
#print axioms sourceBosonPullback_strongContinuous
#print axioms sourceFullGaugePair_strongContinuous

end
end FCP.BFSSSU2PhysicalDomainD2B8C
