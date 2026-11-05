import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4E1BOriginalAYAmbientChargeAction

/-!
BFSS M4F9 H4E2A — source-original AY ambient-output versus
genuine native physical-output Hilbert polarized energy form.

On the *true original native charge natural domain* the original
ambient charge equals physical-output inclusion (strict H4E1B), and
the actual H3B1 inclusion preserves the full complex Hilbert inner
pairing (strict H4E1A). Hence the exact normalized 1/16 polarized
charge-energy forms agree.

Both original charge operators and their source domains are unchanged.
No false onto-ambient unitary, no Hilbert adjoint-square equality,
no independent-model identification or spectral assertion yet.
-/
set_option autoImplicit false
set_option maxHeartbeats 180000

namespace FCP.M4F9H4E2AOriginalAYAmbientNativePolarizedForm
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open FCP.M4F9H3B1OriginalAYNativePhysicalHilbertGraphRebase
open FCP.M4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn
open FCP.M4F9H4E1BOriginalAYAmbientChargeAction
open MeasureTheory Set

/-- Equality of the actual original AY ambient-output and genuine
source-native physical-output polarized Hilbert charge-energy pairings
for any two inputs in the exact source native charge natural domain. -/
theorem pairedOriginalAYAmbientNative_inner_charge_eq
    (u v : pairedGaugeData.physicalSpace)
    (hu : u ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain)
    (hv : v ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain) :
    inner ℂ
      ((originalMinimalPhysicalHilbertChargeColumn
        pairedAlgebraData pairedGaugeData)
        ⟨u, pairedOriginalAmbientCharge_domain_ofNative u hu⟩)
      ((originalMinimalPhysicalHilbertChargeColumn
        pairedAlgebraData pairedGaugeData)
        ⟨v, pairedOriginalAmbientCharge_domain_ofNative v hv⟩) =
    inner ℂ (pairedOriginalNativePhysicalHilbertChargeColumn ⟨u,hu⟩)
      (pairedOriginalNativePhysicalHilbertChargeColumn ⟨v,hv⟩) := by
  have hpair :=
    congrArg₂
      (fun a b : PiLp 2 (fun _ : SpinIndex => FullL2 2) =>
        inner ℂ a b)
      (pairedOriginalAmbientCharge_action_ofNative u hu)
      (pairedOriginalAmbientCharge_action_ofNative v hv)
  exact hpair.trans
    (FCP.M4F9H4E1AOriginalAmbientOutputInnerBridge.pairedPhysicalHilbertOutputsToOriginalAmbient_inner
      (pairedOriginalNativePhysicalHilbertChargeColumn ⟨u,hu⟩)
      (pairedOriginalNativePhysicalHilbertChargeColumn ⟨v,hv⟩))

/-- Exact paper/source 1/16 normalization of the physical charge-energy
polarized form, for the unchanged historical original AY source charge.
This equality is NOT itself an operator-domain or spectral statement. -/
theorem pairedOriginalAYAmbientNative_normalizedForm_eq
    (u v : pairedGaugeData.physicalSpace)
    (hu : u ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain)
    (hv : v ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain) :
    (1 / 16 : ℂ) *
      inner ℂ
        ((originalMinimalPhysicalHilbertChargeColumn
          pairedAlgebraData pairedGaugeData)
          ⟨u, pairedOriginalAmbientCharge_domain_ofNative u hu⟩)
        ((originalMinimalPhysicalHilbertChargeColumn
          pairedAlgebraData pairedGaugeData)
          ⟨v, pairedOriginalAmbientCharge_domain_ofNative v hv⟩) =
    (1 / 16 : ℂ) *
      inner ℂ (pairedOriginalNativePhysicalHilbertChargeColumn ⟨u,hu⟩)
        (pairedOriginalNativePhysicalHilbertChargeColumn ⟨v,hv⟩) := by
  rw [pairedOriginalAYAmbientNative_inner_charge_eq u v hu hv]

#print axioms pairedOriginalAYAmbientNative_inner_charge_eq
#print axioms pairedOriginalAYAmbientNative_normalizedForm_eq
end
end FCP.M4F9H4E2AOriginalAYAmbientNativePolarizedForm
