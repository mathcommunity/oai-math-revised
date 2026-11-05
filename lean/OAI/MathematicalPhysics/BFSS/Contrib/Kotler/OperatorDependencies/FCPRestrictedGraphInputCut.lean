import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentFullCoreGraphClosure

/-!
M4F6 input-restriction architecture. Generic graph restriction and image
lemmas are proved before the concrete original BFSS specialization.
They do not assert that the outputs satisfy the input's physical constraint.
Prospective until the isolated pinned compilation and axiom gate passes.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.RestrictedGraphInputCut
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData

/-- Restrict a core to the preimage of a physical input submodule.
The resulting graph is exactly the unrestricted graph with that input
constraint. No output invariance or injectivity premise is needed. -/
theorem core_graph_input_cut
    {X Y Z : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module ℂ X] [Module ℂ Y] [Module ℂ Z]
    (a : X →ₗ[ℂ] Y) (b : X →ₗ[ℂ] Z) (P : Submodule ℂ Y) :
    (LinearMap.range
      ((a.comp (P.comap a).subtype).prod
        (b.comp (P.comap a).subtype)) : Set (Y × Z)) =
      {p | p ∈ LinearMap.range (a.prod b) ∧ p.1 ∈ P} := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x.val, rfl⟩, x.property⟩
  · rintro ⟨⟨x, rfl⟩, hx⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-- A set-image equality restricts along equivalent predicates. This
lemma is proved for arbitrary maps, before introducing large source
objects or any concrete invariant-core equivalence. -/
theorem image_input_cut
    {A B : Type*} (H : A → B) (S : Set A) (T : Set B)
    (P : A → Prop) (Q : B → Prop)
    (hST : T = H '' S) (hPQ : ∀ p, P p ↔ Q (H p)) :
    {q | q ∈ T ∧ Q q} = H '' {p | p ∈ S ∧ P p} := by
  rw [hST]
  ext q
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hq⟩
    exact ⟨p, ⟨hp, (hPQ p).mpr hq⟩, rfl⟩
  · rintro ⟨p, ⟨hp, hP⟩, rfl⟩
    exact ⟨⟨p, hp, rfl⟩, (hPQ p).mp hP⟩

/-- The literal original GaugeData invariantCore is the comap of its
physicalSpace. Qualify this source equality parametrically before
specializing to the concrete paired SU(2) source data. -/
theorem original_core_graph_input_cut
    {N : ℕ} (M : AlgebraData N) (G : M.GaugeData) :
    (LinearMap.range
      ((coreToL2.comp G.invariantCore.subtype).prod
        (M.chargeVector.comp G.invariantCore.subtype)) :
      Set (FullL2 N × (SpinIndex → FullL2 N))) =
      {p | p ∈ M.fullCoreGraph ∧ p.1 ∈ G.physicalSpace} := by
  exact core_graph_input_cut (coreToL2 (N := N)) M.chargeVector G.physicalSpace

#print axioms core_graph_input_cut
#print axioms image_input_cut
#print axioms original_core_graph_input_cut

end
end FCP.RestrictedGraphInputCut
