import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4E3D4BIndependentNormalizedHistoricalHamiltonianAction

/-!
BFSS H4E3D4C1 — generic, independently strict-qualified Hilbert
partial-operator graph transport under a genuine unitary.

For A and B on possibly DIFFERENT Hilbert spaces, the full domain iff
and witnessed exact action intertwining suffice for an iff on every
point of their literal Mathlib LinearPMap.graph submodules.
No false whole-domain LinearPMap.comp or physical premises.
-/
set_option autoImplicit false
set_option maxHeartbeats 240000

namespace FCP.M4F9H4E3D4C1GenericUnitaryPartialGraphEquivalence
noncomputable section

/-- Full graph membership equivalence follows from actual domain iff
and exact action transport on all natural domain witnesses. -/
theorem genericUnitaryPartialGraph_mem_iff
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (U : X ≃ₗᵢ[ℂ] Y)
    (A : X →ₗ.[ℂ] X)
    (B : Y →ₗ.[ℂ] Y)
    (hDom : ∀ x : X, x ∈ A.domain ↔ U x ∈ B.domain)
    (hAction : ∀ (x : X) (hx : x ∈ A.domain),
      ∃ hy : U x ∈ B.domain,
        B ⟨U x,hy⟩ = U (A ⟨x,hx⟩))
    (x z : X) :
    (x,z) ∈ A.graph ↔ (U x,U z) ∈ B.graph := by
  constructor
  · intro hGraph
    obtain ⟨a, ha, haz⟩ := (LinearPMap.mem_graph_iff A).mp hGraph
    have hx : x ∈ A.domain := by
      simpa only [ha] using a.property
    obtain ⟨hy, hExact⟩ := hAction x hx
    apply (LinearPMap.mem_graph_iff B).mpr
    refine ⟨⟨U x,hy⟩, rfl, ?_⟩
    have hSub : (⟨x,hx⟩ : A.domain) = a :=
      Subtype.ext ha.symm
    calc
      B ⟨U x,hy⟩ = U (A ⟨x,hx⟩) := hExact
      _ = U (A a) := congrArg (fun w : A.domain => U (A w)) hSub
      _ = U z := congrArg U haz
  · intro hGraph
    obtain ⟨b, hb, hbz⟩ := (LinearPMap.mem_graph_iff B).mp hGraph
    have hy : U x ∈ B.domain := by
      simpa only [hb] using b.property
    have hx : x ∈ A.domain := (hDom x).mpr hy
    obtain ⟨hy', hExact⟩ := hAction x hx
    apply (LinearPMap.mem_graph_iff A).mpr
    refine ⟨⟨x,hx⟩, rfl, ?_⟩
    apply U.injective
    have hSub : (⟨U x,hy'⟩ : B.domain) = b :=
      Subtype.ext hb.symm
    calc
      U (A ⟨x,hx⟩) = B ⟨U x,hy'⟩ := hExact.symm
      _ = B b := congrArg (fun w : B.domain => B w) hSub
      _ = U z := hbz

#print axioms genericUnitaryPartialGraph_mem_iff
end
end FCP.M4F9H4E3D4C1GenericUnitaryPartialGraphEquivalence
