import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7GenericClosedRangeOutputsE7G

/-!
M4F7 E7H — abstract CLOSED graph inclusion into an explicit
all-coordinate output submodule predicate.

This lemma deliberately has no BFSS definitions, CAR relations,
fermion space, source transport, or physical claims.  The opaque
graph G is related to the exact product-map range closure by a
supplied equality, never by definitional unfolding.

An E7H gate may qualify these generic support certificates; they
do not constitute an additional source-specific BFSS principal root.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F7GenericOpaqueOutputConstraintE7H
noncomputable section

variable {I V X Y : Type*}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup Y] [Module ℂ Y]

/-- Exact all-coordinate output constraint for an abstract complex
physical submodule; no charge formula is inserted. -/
def allOutputConstraint (P : Submodule ℂ Y) :
    Set (X × (I → Y)) :=
  {p | ∀ i : I, p.2 i ∈ P}

/-- Unfold only the small abstract output predicate. -/
theorem mem_allOutputConstraint_iff
    (P : Submodule ℂ Y) (p : X × (I → Y)) :
    p ∈ allOutputConstraint (I := I) P ↔
      ∀ i : I, p.2 i ∈ P := Iff.rfl

variable [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
variable [TopologicalSpace Y]

/-- For any supplied opaque relation G, exact equality to the
original product-range closure transfers all output membership. -/
theorem opaque_closed_product_range_subset_allOutputConstraint
    (F : V →ₗ[ℂ] X)
    (Q : V →ₗ[ℂ] (I → Y))
    (P : Submodule ℂ Y)
    (hP : IsClosed (P : Set Y))
    (hQ : ∀ (v : V) (i : I), (Q v) i ∈ P)
    (G : Set (X × (I → Y)))
    (hG : G = closure (LinearMap.range (F.prod Q) :
      Set (X × (I → Y)))) :
    G ⊆ allOutputConstraint (I := I) P := by
  intro p hp
  change ∀ i : I, p.2 i ∈ P
  have hp' : p ∈ closure (LinearMap.range (F.prod Q) :
      Set (X × (I → Y))) := by
    rw [← hG]
    exact hp
  intro i
  exact FCP.M4F7GenericClosedRangeOutputsE7G.closed_product_range_output_mem
    F Q P hP hQ p hp' i

#print axioms allOutputConstraint
#print axioms mem_allOutputConstraint_iff
#print axioms opaque_closed_product_range_subset_allOutputConstraint

end
end FCP.M4F7GenericOpaqueOutputConstraintE7H
