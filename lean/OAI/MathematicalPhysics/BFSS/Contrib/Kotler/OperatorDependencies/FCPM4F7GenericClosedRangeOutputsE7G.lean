import Mathlib

/-!
M4F7 E7G — universal closed product-graph output restriction.

This is intentionally free of BFSS source/independent definitions,
48-Majorana operators, subgroup actions, CAR relations, source
transport, E2 closure or any Hamiltonian. No statement about the
actual physical BFSS closed graph is established by this helper alone.

Given any two complex-linear maps F, Q from a common domain into X
and I-indexed Y output columns, if every smooth/core output of Q
belongs to a CLOSED submodule P of Y, then every output coordinate of
every point in the ordinary topological closure of range(F.prod Q)
belongs to P. The proof is purely topological and uses continuity
of the product projection and coordinate evaluation.

E7G is a supporting proof interface. Its acceptance must not
be counted as an additional original-source BFSS principal root.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F7GenericClosedRangeOutputsE7G
noncomputable section

variable {I V X Y : Type*}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
variable [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]

/-- Fully abstract physical-output restriction under ordinary closure
of the L²×column graph, with no assumption on injectivity or density. -/
theorem closed_product_range_output_mem
    (F : V →ₗ[ℂ] X)
    (Q : V →ₗ[ℂ] (I → Y))
    (P : Submodule ℂ Y)
    (hP : IsClosed (P : Set Y))
    (hQ : ∀ (v : V) (i : I), (Q v) i ∈ P)
    (p : X × (I → Y))
    (hp : p ∈ closure (LinearMap.range (F.prod Q) :
      Set (X × (I → Y))))
    (i : I) :
    p.2 i ∈ P := by
  have hclosed : IsClosed
      {z : X × (I → Y) | z.2 i ∈ P} :=
    hP.preimage ((continuous_apply i).comp continuous_snd)
  have hraw :
      (LinearMap.range (F.prod Q) :
        Set (X × (I → Y))) ⊆
        {z : X × (I → Y) | z.2 i ∈ P} := by
    intro z hz
    rcases hz with ⟨v, rfl⟩
    exact hQ v i
  exact (closure_minimal hraw hclosed) hp

#print axioms closed_product_range_output_mem

end
end FCP.M4F7GenericClosedRangeOutputsE7G
