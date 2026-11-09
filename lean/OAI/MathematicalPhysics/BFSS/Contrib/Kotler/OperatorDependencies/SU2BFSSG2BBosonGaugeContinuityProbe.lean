import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG2ABosonGaugeProbe

/-!
# BFSS SU(2) G2-B — joint continuity of the genuine bosonic gauge action

G2-A (Gate #92) proved the exact GaugeGroup 2 homomorphism into real
linear isometry equivalences and its pinned boson_adjoint law. This
step proves the remaining boson_continuous field for that same action.

The argument follows the pinned upstream BFSS/SliceIntegrals matrix
continuity method, with the actual special-unitary rather than larger
unitary group and no new AlgebraData or GaugeData assumption.

No fermionic gauge action or spectral conclusion is asserted.
-/

namespace FCP.BFSSSU2GaugeG2B
noncomputable section

open Matrix
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG2A
open scoped Matrix.Norms.L2Operator

private abbrev M : AlgebraData 2 := pairedAlgebraData

/-- The actual G2-A bosonic GaugeGroup 2 action satisfies the exact
joint-continuity field of the upstream AlgebraData.GaugeData type. -/
theorem bosonGauge_continuous :
    Continuous (fun z : GaugeGroup 2 × Boson 2 => bosonGauge z.1 z.2) := by
  change Continuous (fun z : GaugeGroup 2 × Boson 2 =>
    M.gaugeConjugate (z.1 : ColorMatrix 2) z.2)
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro p
  change Continuous (fun z : GaugeGroup 2 × Boson 2 =>
    M.colorExtract ((z.1 : ColorMatrix 2) *
      M.colorEmbed (spatialColor z.2 p.1) *
      (z.1 : ColorMatrix 2)ᴴ) p.2)
  have hspatial :
      Continuous (fun z : GaugeGroup 2 × Boson 2 =>
        spatialColor z.2 p.1) := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro A
    change Continuous (fun z : GaugeGroup 2 × Boson 2 => z.2 (p.1, A))
    exact (PiLp.continuous_apply 2 _ (p.1, A)).comp continuous_snd
  exact (PiLp.continuous_apply 2 _ p.2).comp
    (M.colorExtract.toContinuousLinearMap.continuous.comp
      (((continuous_subtype_val.comp continuous_fst).mul
        (M.colorEmbed.toContinuousLinearMap.continuous.comp hspatial)).mul
        (continuous_subtype_val.comp continuous_fst).star))

#print axioms bosonGauge_continuous

end
end FCP.BFSSSU2GaugeG2B
