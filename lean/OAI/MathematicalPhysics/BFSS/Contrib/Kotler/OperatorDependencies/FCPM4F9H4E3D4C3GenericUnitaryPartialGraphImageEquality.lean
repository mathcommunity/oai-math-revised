import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4E3D4C2ActualIndependentHistoricalUnitaryGraphEquivalence

/-!
BFSS H4E3D4C3 — generic exact SUBMODULE image equality for real
Mathlib LinearPMap graphs under a genuine complex Hilbert unitary.
This upgrades the accepted C1 full pointwise graph membership iff
to equality of transported complete graph submodules. Unlike source
equations on different Hilbert carriers, the map is the authentic
linear product of the same unitary U on both graph coordinates.
-/
set_option autoImplicit false
set_option maxHeartbeats 240000

namespace FCP.M4F9H4E3D4C3GenericUnitaryPartialGraphImageEquality
noncomputable section

/-- Exact complete graph SUBMODULE image under U × U.
No everywhere-defined partial composition, kernel completion,
core restriction, or additional spectral hypotheses. -/
theorem genericUnitaryPartialGraph_map_eq
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (U : X ≃ₗᵢ[ℂ] Y)
    (A : X →ₗ.[ℂ] X)
    (B : Y →ₗ.[ℂ] Y)
    (hDom : ∀ x : X, x ∈ A.domain ↔ U x ∈ B.domain)
    (hAction : ∀ (x : X) (hx : x ∈ A.domain),
      ∃ hy : U x ∈ B.domain,
        B ⟨U x,hy⟩ = U (A ⟨x,hx⟩)) :
    A.graph.map
      ((U.toLinearEquiv.toLinearMap).prodMap
        U.toLinearEquiv.toLinearMap) = B.graph := by
  apply Submodule.ext
  intro q
  constructor
  · intro hq
    obtain ⟨p,hp,hpq⟩ := hq
    have hg : (U p.1,U p.2) ∈ B.graph :=
      (FCP.M4F9H4E3D4C1GenericUnitaryPartialGraphEquivalence.genericUnitaryPartialGraph_mem_iff
        U A B hDom hAction p.1 p.2).mp hp
    have heq : (U p.1,U p.2) = q := by
      change (U p.1,U p.2) = q at hpq
      exact hpq
    exact heq ▸ hg
  · intro hq
    let p : X × X := (U.symm q.1,U.symm q.2)
    have hImage : (U p.1,U p.2) ∈ B.graph := by
      simpa only [p, U.apply_symm_apply] using hq
    have hp : p ∈ A.graph :=
      (FCP.M4F9H4E3D4C1GenericUnitaryPartialGraphEquivalence.genericUnitaryPartialGraph_mem_iff
        U A B hDom hAction p.1 p.2).mpr hImage
    refine ⟨p,hp,?_⟩
    change (U p.1,U p.2) = q
    simp only [p, U.apply_symm_apply]

#print axioms genericUnitaryPartialGraph_map_eq
end
end FCP.M4F9H4E3D4C3GenericUnitaryPartialGraphImageEquality
