import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B14ExactClosedChargeQuadraticEnergyProbe

/-!
# BFSS SU2 D2B15 — quantitative closed-charge energy and form-domain completeness

PROSPECTIVE until exact pinned Lean Actions compiler and axiom smoke succeeds.

For the actual ORIGINAL GaugeData gauge-restricted closed charge column:
* each sixteen-charge L2 output is bounded by exactly 16 times the
  closed nonnegative q = (1/16) sum ||Qα ψ||²;
* its genuine source graph is complete as a closed subspace of the
  original Hilbert product;
* convergence in the physical L² input and all sixteen charge outputs
  produces an element of the actual operator domain with the
  expected closed output.

Because the charge index is finite, these are the analytic graph
closedness and quantitative energy controls underlying the familiar
closed positive form norm. No form representation theorem, self-adjoint
Hamiltonian, maximal-domain equality, or spectral claim is asserted.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B15
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2B11
open FCP.BFSSSU2PhysicalDomainD2B12
open FCP.BFSSSU2PhysicalDomainD2B14
open Finset MeasureTheory Set Filter
open scoped Topology

variable {N : ℕ} (M : AlgebraData N) (G : M.GaugeData)

/-- Each true closed charge component is quantitatively controlled
by the exact 1/16-normalized closed BFSS charge quadratic energy.
This is the key finite-column estimate needed for form convergence. -/
theorem sourceClosedPhysicalCharge_component_sq_le_form
    (u : (sourceClosedPhysicalChargeColumn M G).domain)
    (α : SpinIndex) :
    ‖(sourceClosedPhysicalChargeColumn M G u) α‖^2 ≤
      16 * sourceClosedPhysicalChargeEnergy M G u := by
  have hs :
      ‖(sourceClosedPhysicalChargeColumn M G u) α‖^2 ≤
      ∑ β : SpinIndex,
        ‖(sourceClosedPhysicalChargeColumn M G u) β‖^2 := by
    simpa using
      (Finset.single_le_sum
        (f := fun β : SpinIndex =>
          ‖(sourceClosedPhysicalChargeColumn M G u) β‖ ^ 2)
        (s := Finset.univ)
        (fun β hβ => sq_nonneg _)
        (Finset.mem_univ α))
  calc
    _ ≤ ∑ β : SpinIndex,
          ‖(sourceClosedPhysicalChargeColumn M G u) β‖^2 := hs
    _ = 16 * sourceClosedPhysicalChargeEnergy M G u := by
          unfold sourceClosedPhysicalChargeEnergy
          ring

/-- The actual pinned gauge-restricted charge graph is complete,
because it is a closed subspace of the source full-L2 × 16-L2 Hilbert
product. This is a theorem about the REAL source graph. -/
theorem sourceClosedPhysicalCharge_graph_complete :
    CompleteSpace (G.deformedModelGraph 1 0) := by
  let : IsClosed (G.deformedModelGraph 1 0 :
      Set (FullL2 N × (SpinIndex → FullL2 N))) :=
    sourceRestrictedPhysicalGraph_isClosed M G
  infer_instance

/-- Closedness in the exact original coordinate-by-coordinate
analytic form: if L2 inputs converge and all sixteen L2 charge
outputs converge, the limits are a genuine point of the CLOSED source
operator graph. No unbounded pointwise evaluation is used. -/
theorem sourceClosedPhysicalCharge_componentwise_limit
    (u : ℕ → (sourceClosedPhysicalChargeColumn M G).domain)
    (ψ : FullL2 N) (y : SpinIndex → FullL2 N)
    (hu : Tendsto (fun n => (u n : FullL2 N)) atTop (𝓝 ψ))
    (hy : ∀ α : SpinIndex,
      Tendsto (fun n => (sourceClosedPhysicalChargeColumn M G (u n)) α)
        atTop (𝓝 (y α))) :
    ∃ v : (sourceClosedPhysicalChargeColumn M G).domain,
      (v : FullL2 N) = ψ ∧
        sourceClosedPhysicalChargeColumn M G v = y := by
  let Q := sourceClosedPhysicalChargeColumn M G
  have hpair :
      Tendsto (fun n => ((u n : FullL2 N), Q (u n)))
        atTop (𝓝 (ψ,y)) :=
    Filter.Tendsto.prodMk_nhds hu (tendsto_pi_nhds.mpr hy)
  have hpoint :
      (ψ,y) ∈ Q.graph := by
    apply (sourceClosedPhysicalChargeColumn_isClosed M G).mem_of_tendsto hpair
    filter_upwards [] with n
    exact Q.mem_graph (u n)
  let v : Q.domain := ⟨ψ, Q.mem_domain_of_mem_graph hpoint⟩
  refine ⟨v, rfl, ?_⟩
  exact Q.mem_graph_snd_inj (Q.mem_graph v) hpoint rfl

#print axioms sourceClosedPhysicalCharge_component_sq_le_form
#print axioms sourceClosedPhysicalCharge_graph_complete
#print axioms sourceClosedPhysicalCharge_componentwise_limit

end
end FCP.BFSSSU2PhysicalDomainD2B15
