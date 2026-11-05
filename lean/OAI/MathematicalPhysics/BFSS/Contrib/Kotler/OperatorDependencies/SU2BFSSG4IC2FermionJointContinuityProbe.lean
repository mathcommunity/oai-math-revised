import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4IC1FermionParameterContinuityProbe

/-!
# BFSS SU(2) G4-I-C2 — exact joint continuity of the fermionic gauge action

The true source-bound Fock/BFSS SU(2) representation is the G4-E
`fermionGaugeUnitaryHom` on the ACTUAL Hilbert type `Fermion 2`.

Gate #121 established parameter continuity for every fixed vector.
This proves the literal missing joint `GaugeData.fermion_continuous`
proposition using an explicit isometry/triangle estimate.

No change of action, unproved norm estimate or alternative type.
The six-field AlgebraData.GaugeData itself remains to be assembled.
-/

namespace FCP.BFSSSU2GaugeG4IC2
noncomputable section

open OAI.BFSSQuantum
open Filter
open scoped Topology
open FCP.BFSSSU2GaugeG4E FCP.BFSSSU2GaugeG4IC1

/-- The genuine SU(2) gauge action is simultaneously continuous
in the group element and the exact 2^24-dimensional Hilbert state.

The only analytic inputs are G4-I-C1 parameter continuity at
a FIXED vector and G4-E norm-preserving complex-linearity for
the same action, yielding

  ‖U(g')v' - U(g)v‖ ≤ ‖v'-v‖ + ‖U(g')v-U(g)v‖.

This is the literal missing fermion_continuous field of the
pinned upstream AlgebraData.GaugeData for SU(2), but the
complete structure is NOT claimed by this theorem alone. -/
theorem fermionGauge_jointContinuous :
    Continuous (fun z : GaugeGroup 2 × Fermion 2 =>
      fermionGaugeUnitaryHom z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨g, v⟩
  have hstate : Continuous (fun z : GaugeGroup 2 × Fermion 2 =>
      ‖z.2 - v‖) :=
    (continuous_snd.sub continuous_const).norm
  have hparameter : Continuous (fun z : GaugeGroup 2 × Fermion 2 =>
      ‖fermionGaugeUnitaryHom z.1 v - fermionGaugeUnitaryHom g v‖) :=
    (((fermionGauge_parameter_continuous v).comp continuous_fst).sub
      continuous_const).norm
  have hbound0 : Tendsto (fun z : GaugeGroup 2 × Fermion 2 =>
      ‖z.2 - v‖ +
        ‖fermionGaugeUnitaryHom z.1 v - fermionGaugeUnitaryHom g v‖)
        (𝓝 (g, v)) (𝓝 (0 : ℝ)) := by
    have h : Tendsto (fun z : GaugeGroup 2 × Fermion 2 =>
        ‖z.2 - v‖ +
          ‖fermionGaugeUnitaryHom z.1 v - fermionGaugeUnitaryHom g v‖)
        (𝓝 (g, v))
        (𝓝 (‖v - v‖ +
          ‖fermionGaugeUnitaryHom g v - fermionGaugeUnitaryHom g v‖)) :=
      (hstate.add hparameter).continuousAt
    simpa only [sub_self, norm_zero, zero_add] using h
  have hbound (z : GaugeGroup 2 × Fermion 2) :
      ‖fermionGaugeUnitaryHom z.1 z.2 -
          fermionGaugeUnitaryHom g v‖ ≤
        ‖z.2 - v‖ +
          ‖fermionGaugeUnitaryHom z.1 v -
            fermionGaugeUnitaryHom g v‖ := by
    have hsplit :
        fermionGaugeUnitaryHom z.1 z.2 -
            fermionGaugeUnitaryHom g v =
          fermionGaugeUnitaryHom z.1 (z.2 - v) +
            (fermionGaugeUnitaryHom z.1 v -
              fermionGaugeUnitaryHom g v) := by
      rw [map_sub]
      abel
    rw [hsplit]
    calc
      ‖fermionGaugeUnitaryHom z.1 (z.2 - v) +
          (fermionGaugeUnitaryHom z.1 v -
            fermionGaugeUnitaryHom g v)‖ ≤
        ‖fermionGaugeUnitaryHom z.1 (z.2 - v)‖ +
          ‖fermionGaugeUnitaryHom z.1 v -
            fermionGaugeUnitaryHom g v‖ :=
              norm_add_le _ _
      _ = ‖z.2 - v‖ +
          ‖fermionGaugeUnitaryHom z.1 v -
            fermionGaugeUnitaryHom g v‖ := by
        rw [LinearIsometryEquiv.norm_map]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hbound hbound0

#print axioms fermionGauge_jointContinuous

end
end FCP.BFSSSU2GaugeG4IC2
