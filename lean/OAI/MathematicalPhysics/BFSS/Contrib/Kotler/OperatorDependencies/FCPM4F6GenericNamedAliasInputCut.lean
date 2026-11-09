import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPRestrictedGraphInputCut

/-!
M4F6 B1 — abstract alias-aware input-cut certificate.

The physical-space preimage and full-core graph are represented by *opaque*
abstract complex submodules S and G, and are identified only by explicit
equations hS and hG. The proof never specializes to the independent BFSS L²,
invariant-core, theta, or charge definitions.

This is a supporting lemma, not the original independent C2 theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F6GenericNamedAliasInputCut
noncomputable section

open FCP.RestrictedGraphInputCut

/-- The ordinary abstract graph input restriction, with separately named
core and graph submodule aliases connected by explicit proof certificates. -/
theorem core_graph_input_cut_with_named_aliases
    {X Y Z : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module ℂ X] [Module ℂ Y] [Module ℂ Z]
    (a : X →ₗ[ℂ] Y) (b : X →ₗ[ℂ] Z) (P : Submodule ℂ Y)
    (S : Submodule ℂ X) (G : Submodule ℂ (Y × Z))
    (hS : S = P.comap a)
    (hG : G = LinearMap.range (a.prod b)) :
    (LinearMap.range
      ((a.comp S.subtype).prod (b.comp S.subtype)) :
      Set (Y × Z)) =
      {p | p ∈ G ∧ p.1 ∈ P} := by
  subst S
  subst G
  exact core_graph_input_cut a b P

#print axioms core_graph_input_cut_with_named_aliases
#check core_graph_input_cut_with_named_aliases

end
end FCP.M4F6GenericNamedAliasInputCut
