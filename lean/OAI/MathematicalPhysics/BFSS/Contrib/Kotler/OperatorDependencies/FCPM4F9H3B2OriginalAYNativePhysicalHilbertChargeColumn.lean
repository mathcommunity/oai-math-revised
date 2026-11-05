import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H3B1OriginalAYNativePhysicalHilbertGraphRebase

/-!
BFSS M4F9 H3B2 — ACTUAL original paired AY charge on original
physical Hilbert INPUT and native physical PiLp2 OUTPUT, with the
exact original AY natural domain. This is the source-side operator
needed before independent/source unitary Hilbert intertwining.

H3B1 supplies literal coordinate inclusion and exact source AY graph
preimage; H3A supplies physicality of all actual AY graph outputs
under explicit original-independent matching witnesses. Definitions
of AY, independent E2, gauge, charge, and Hamiltonian are unchanged.
No false surjectivity onto ambient source FullL2 direct sum.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000

namespace FCP.M4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open FCP.M4F9H3AOriginalPairedPhysicalChargeOutputConstraint
open FCP.M4F9H3B1OriginalAYNativePhysicalHilbertGraphRebase
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
  theta α A * theta β B + theta β B * theta α A =
    (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
variable (hHermitian : ∀ α A, (theta α A).IsSymmetric)
variable (color : ColorIndex 2 → ColorMatrix 2)
variable (gamma : SpaceIndex → GammaMatrix)
variable (J : E ≃ₗᵢ[ℂ] Fermion 2)
variable (hColor : color = pairedAlgebraData.color)
variable (hGamma : gamma = pairedAlgebraData.gamma)
variable (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))

/-- Native physical-output AY graph is single-valued because the
unchanged AY ORIGINAL ambient partial charge graph is single-valued,
and H3B1's literal physical→ambient output inclusion is injective. -/
theorem pairedOriginalPhysicalHilbertChargeGraph_vertical :
    ∀ p : pairedGaugeData.physicalSpace ×
      PiLp 2 (fun _ : SpinIndex => pairedGaugeData.physicalSpace),
      p ∈ pairedOriginalPhysicalHilbertChargeGraph →
      p.1 = 0 → p.2 = 0 := by
  rintro ⟨u,y⟩ hp hu
  have hAY :
      (u, pairedPhysicalHilbertOutputsToOriginalAmbient y) ∈
        (originalMinimalPhysicalHilbertChargeColumn
          pairedAlgebraData pairedGaugeData).graph :=
    (pairedOriginalPhysicalHilbertChargeGraph_mem_iff (u,y)).mp hp
  have hzero :
      pairedPhysicalHilbertOutputsToOriginalAmbient y = 0 :=
    (originalMinimalPhysicalHilbertChargeColumn
      pairedAlgebraData pairedGaugeData).graph_fst_eq_zero_snd hAY hu
  apply pairedPhysicalHilbertOutputsToOriginalAmbient_injective
  simpa only [map_zero] using hzero

/-- The ACTUAL original AY charge partial operator with true
source gauge-physical Hilbert sixteen-output codomain. Graph is the
literal preimage of AY's separately original-specified graph. -/
noncomputable def pairedOriginalNativePhysicalHilbertChargeColumn :
    pairedGaugeData.physicalSpace →ₗ.[ℂ]
      PiLp 2 (fun _ : SpinIndex => pairedGaugeData.physicalSpace) :=
  pairedOriginalPhysicalHilbertChargeGraph.toLinearPMap

theorem pairedOriginalNativePhysicalHilbertChargeColumn_graph_eq :
    pairedOriginalNativePhysicalHilbertChargeColumn.graph =
      pairedOriginalPhysicalHilbertChargeGraph := by
  exact Submodule.toLinearPMap_graph_eq _
    pairedOriginalPhysicalHilbertChargeGraph_vertical

/-!
A bounded projection interface: the domain of the partial linear map
built from the H3B1 physical graph is the first-coordinate projection
of that graph. Prove this independently of the original AY source.
This avoids rewriting an enormous closed-source graph in the final
natural-domain proof. It is a supporting proof, not a fifth principal root.
-/
private theorem nativeDomain_iff_exists_physicalGraph
    (u : pairedGaugeData.physicalSpace) :
    u ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain ↔
      ∃ v : PiLp 2 (fun _ : SpinIndex => pairedGaugeData.physicalSpace),
        (u, v) ∈ pairedOriginalPhysicalHilbertChargeGraph := by
  change u ∈ pairedOriginalPhysicalHilbertChargeGraph.toLinearPMap.domain ↔ _
  rw [Submodule.toLinearPMap_domain]
  constructor
  · intro hu
    rcases (Submodule.mem_map).mp hu with ⟨p, hp, hpu⟩
    rcases p with ⟨x, v⟩
    change x = u at hpu
    subst x
    exact ⟨v, hp⟩
  · rintro ⟨v, hv⟩
    exact (Submodule.mem_map).mpr ⟨(u, v), hv, rfl⟩

-- Matching original-independent CAR and gauge witnesses only enter the
-- *theorem* discharging the real AY graph output physicality; they do
-- not enter either source-side charge or graph definitions.
include theta hCAR hHermitian color gamma J hColor hGamma hJ

/-- The native SOURCE physical-output charge has *exactly* the same
natural physical input domain as the ORIGINAL AY ambient-output charge.
The reverse implication relies on the strictly accepted original AY
physical output constraint H3A; no core-only or assumed domain equality. -/
theorem pairedOriginalNativePhysicalHilbertChargeColumn_domain_iff
    (u : pairedGaugeData.physicalSpace) :
    u ∈ pairedOriginalNativePhysicalHilbertChargeColumn.domain ↔
      u ∈ (originalMinimalPhysicalHilbertChargeColumn
        pairedAlgebraData pairedGaugeData).domain := by
  constructor
  · intro hu
    obtain ⟨v, hv⟩ := (nativeDomain_iff_exists_physicalGraph u).mp hu
    exact (LinearPMap.mem_domain_iff).mpr
      ⟨pairedPhysicalHilbertOutputsToOriginalAmbient v,
        (pairedOriginalPhysicalHilbertChargeGraph_mem_iff (u,v)).mp hv⟩
  · intro hu
    obtain ⟨w,hw⟩ := (LinearPMap.mem_domain_iff).mp hu
    have hout (α : SpinIndex) :
        w α ∈ pairedGaugeData.physicalSpace :=
      pairedOriginalMinimalPhysicalHilbertChargeGraph_outputs_physical
        theta hCAR hHermitian color gamma J hColor hGamma hJ
        (u,w) (by
          rwa [originalMinimalPhysicalHilbertChargeColumn_graph_eq] at hw)
        α
    let v : PiLp 2 (fun _ : SpinIndex => pairedGaugeData.physicalSpace) :=
      WithLp.toLp 2 (fun α : SpinIndex =>
        (⟨w α,hout α⟩ : pairedGaugeData.physicalSpace))
    have hv : pairedPhysicalHilbertOutputsToOriginalAmbient v = w := by
      apply PiLp.ext
      intro α
      rfl
    have hphysical : (u,v) ∈ pairedOriginalPhysicalHilbertChargeGraph :=
      (pairedOriginalPhysicalHilbertChargeGraph_mem_iff (u,v)).mpr
        (by simpa only [hv] using hw)
    exact (nativeDomain_iff_exists_physicalGraph u).mpr ⟨v, hphysical⟩

#print axioms pairedOriginalPhysicalHilbertChargeGraph_vertical
#print axioms pairedOriginalNativePhysicalHilbertChargeColumn
#print axioms pairedOriginalNativePhysicalHilbertChargeColumn_graph_eq
#print axioms pairedOriginalNativePhysicalHilbertChargeColumn_domain_iff

end
end FCP.M4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn
