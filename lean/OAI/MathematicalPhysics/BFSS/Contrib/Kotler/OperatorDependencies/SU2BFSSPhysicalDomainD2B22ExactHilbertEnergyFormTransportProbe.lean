import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B21SelfAdjointChargeSquareProbe
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# BFSS SU(2) D2B22 — exact 1/16 source closed-energy transport

PROSPECTIVE until exact pinned CI Lean 4.34.1 + axiom gate passes.

The true Hilbert-valued physical charge T is the *same* original
source closed graph as D2B12, transported along the canonical physical
input inclusion and PiLp(2) ↔ 16-charge source output equivalence.

We identify on ALL of Dom(T), not merely the smooth core:
   (1/16) ‖Tψ‖² = D2B14's exact original closed physical charge energy.

This does not yet identify the closed quadratic form's associated
self-adjoint Hamiltonian, or the manuscript's abstract representation.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B22
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2B12
open FCP.BFSSSU2PhysicalDomainD2B14
open FCP.BFSSSU2PhysicalDomainD2B16
open FCP.BFSSSU2PhysicalDomainD2B17
open FCP.BFSSSU2PhysicalDomainD2B21
open Finset

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- The form induced by the *genuine* physical Hilbert column has
the manuscript's exact coefficient. Its form domain is Dom(T). -/
noncomputable def sourcePhysicalHilbertChargeEnergy
    (u : (sourcePhysicalHilbertChargeColumn M G).domain) : ℝ :=
  (1 / 16 : ℝ) * ‖sourcePhysicalHilbertChargeColumn M G u‖ ^ 2

/-- The physical Hilbert charge column has precisely the SAME
graph point in the source, after canonical identifications. -/
theorem sourcePhysicalHilbertCharge_on_originalGraph
    (u : (sourcePhysicalHilbertChargeColumn M G).domain) :
    (((u : G.physicalSpace) : FullL2 2),
       sourceChargeOutputHilbertEquiv (sourcePhysicalHilbertChargeColumn M G u)) ∈
      G.deformedModelGraph 1 0 := by
  have hHilbert : ((u : G.physicalSpace),
      sourcePhysicalHilbertChargeColumn M G u) ∈
      sourcePhysicalHilbertChargeGraph M G := by
    rw [← sourcePhysicalHilbertChargeColumn_graph_eq M G]
    exact (sourcePhysicalHilbertChargeColumn M G).mem_graph u
  have hrebased :
      ((u : G.physicalSpace),
        sourceChargeOutputHilbertEquiv (sourcePhysicalHilbertChargeColumn M G u)) ∈
        sourcePhysicalRebasedChargeGraph M G :=
    (sourcePhysicalHilbertChargeGraph_mem_iff M G _).mp hHilbert
  exact (sourcePhysicalRebasedChargeGraph_mem_iff M G _).mp hrebased

/-- Every state in the *true* Hilbert charge domain is canonically
in the ORIGINAL D2B12 closed source charge domain. -/
noncomputable def sourcePhysicalHilbertToClosedChargeDomain
    (u : (sourcePhysicalHilbertChargeColumn M G).domain) :
      (sourceClosedPhysicalChargeColumn M G).domain :=
  ⟨((u : G.physicalSpace) : FullL2 2), by
    apply LinearPMap.mem_domain_of_mem_graph
    rw [sourceClosedPhysicalChargeColumn_graph_eq M G]
    exact sourcePhysicalHilbertCharge_on_originalGraph M G u⟩

/-- The actual output is the original source sixteen-charge column:
no replacement dynamics or gauge assumption. -/
theorem sourcePhysicalHilbertToClosedCharge_output
    (u : (sourcePhysicalHilbertChargeColumn M G).domain) :
    sourceClosedPhysicalChargeColumn M G
      (sourcePhysicalHilbertToClosedChargeDomain M G u) =
    sourceChargeOutputHilbertEquiv (sourcePhysicalHilbertChargeColumn M G u) := by
  let Q := sourceClosedPhysicalChargeColumn M G
  have h1 : ((sourcePhysicalHilbertToClosedChargeDomain M G u : FullL2 2),
        Q (sourcePhysicalHilbertToClosedChargeDomain M G u)) ∈ Q.graph :=
    Q.mem_graph _
  have h2 : ((sourcePhysicalHilbertToClosedChargeDomain M G u : FullL2 2),
        sourceChargeOutputHilbertEquiv (sourcePhysicalHilbertChargeColumn M G u)) ∈
        Q.graph := by
    rw [sourceClosedPhysicalChargeColumn_graph_eq M G]
    exact sourcePhysicalHilbertCharge_on_originalGraph M G u
  exact Q.mem_graph_snd_inj h1 h2 rfl

/-- Abstract mathematical Hilbert-sum identity. Keep the concrete
BFSS source module OUT of norm elaboration, exactly as the successful
abstract mathematical gate/physical instantiation pattern. -/
theorem genericPiLpHilbert_norm_sq_sum
    {ι : Type*} [Fintype ι] {H : ι → Type*}
    [∀ i, NormedAddCommGroup (H i)]
    [∀ i, InnerProductSpace ℂ (H i)]
    (y : PiLp 2 H) :
    ‖y‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 H y

/-- Source equivalence only changes the representation of the same
sixteen coordinates; the actual ℓ² norm is inherited from PiLp. -/
theorem sourceChargeHilbertOutput_norm_sq_sum (y : SourceChargeHilbertOutput) :
    ‖y‖ ^ 2 =
      ∑ α : SpinIndex, ‖(sourceChargeOutputHilbertEquiv y) α‖ ^ 2 := by
  have hnorm : ‖y‖ ^ 2 = ∑ α : SpinIndex, ‖y α‖ ^ 2 :=
    genericPiLpHilbert_norm_sq_sum y
  rw [hnorm]
  apply Finset.sum_congr rfl
  intro α hα
  rfl

/-- The exact original source form energy and the physical Hilbert
form energy AGREE on all of the source-closed charge domain, not
merely on a test core. -/
theorem sourcePhysicalHilbertChargeEnergy_eq_sourceClosed
    (u : (sourcePhysicalHilbertChargeColumn M G).domain) :
    sourcePhysicalHilbertChargeEnergy M G u =
      sourceClosedPhysicalChargeEnergy M G
        (sourcePhysicalHilbertToClosedChargeDomain M G u) := by
  unfold sourcePhysicalHilbertChargeEnergy sourceClosedPhysicalChargeEnergy
  rw [sourceChargeHilbertOutput_norm_sq_sum]
  rw [sourcePhysicalHilbertToClosedCharge_output M G u]

/-- The exact normalized physical Hilbert energy is nonnegative. -/
theorem sourcePhysicalHilbertChargeEnergy_nonneg
    (u : (sourcePhysicalHilbertChargeColumn M G).domain) :
    0 ≤ sourcePhysicalHilbertChargeEnergy M G u := by
  rw [sourcePhysicalHilbertChargeEnergy_eq_sourceClosed M G u]
  exact sourceClosedPhysicalChargeEnergy_nonneg M G _

#print axioms sourcePhysicalHilbertCharge_on_originalGraph
#print axioms sourcePhysicalHilbertToClosedCharge_output
#print axioms genericPiLpHilbert_norm_sq_sum
#print axioms sourceChargeHilbertOutput_norm_sq_sum
#print axioms sourcePhysicalHilbertChargeEnergy_eq_sourceClosed
#print axioms sourcePhysicalHilbertChargeEnergy_nonneg

end
end FCP.BFSSSU2PhysicalDomainD2B22
