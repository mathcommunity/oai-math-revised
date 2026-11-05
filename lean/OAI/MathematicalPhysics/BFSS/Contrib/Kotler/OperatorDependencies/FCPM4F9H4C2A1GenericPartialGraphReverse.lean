import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4C1BSourceDomainIndependentNativeRecovery

/-!
BFSS M4F9 H4C2A1 — abstract partial linear operator graph principle.
The reverse graph follows from one reverse DOMAIN implication, forward
GRAPH inclusion, source graph single-valuedness, and two inverse laws.
No BFSS/Clifford/gauge/L2 unfold in this proof. This is a genuine generic
operator lemma to be instantiated separately on the original AY source
and the J-free native E2 operator.
-/
set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F9H4C2A1GenericPartialGraphReverse
noncomputable section

variable {X X' Y Y' : Type*}
variable [AddCommGroup X] [Module ℂ X]
variable [AddCommGroup X'] [Module ℂ X']
variable [AddCommGroup Y] [Module ℂ Y]
variable [AddCommGroup Y'] [Module ℂ Y']

/-- Reverse GRAPH from reverse DOMAIN + forward GRAPH, via source
single-valuedness. U and V need only the explicitly stated inverse
laws; they are instantiated with genuine Hilbert unitaries at BFSS. -/
theorem partialGraph_reverse_of_domain_forward
    (f : X →ₗ.[ℂ] Y) (g : X' →ₗ.[ℂ] Y')
    (U : X → X') (Ui : X' → X)
    (V : Y → Y') (Vi : Y' → Y)
    (hU : ∀ x : X', U (Ui x) = x)
    (hV : ∀ y : Y, Vi (V y) = y)
    (hDomain : ∀ x : X', x ∈ g.domain → Ui x ∈ f.domain)
    (hForward : ∀ x : X, ∀ y : Y,
      (x, y) ∈ f.graph → (U x, V y) ∈ g.graph)
    (p : X' × Y')
    (hp : p ∈ g.graph) :
    (Ui p.1, Vi p.2) ∈ f.graph := by
  have hi : Ui p.1 ∈ f.domain :=
    hDomain p.1 (LinearPMap.mem_domain_of_mem_graph hp)
  obtain ⟨y, hy⟩ := (LinearPMap.mem_domain_iff).mp hi
  have hforward : (U (Ui p.1), V y) ∈ g.graph :=
    hForward (Ui p.1) y hy
  have houtput : V y = p.2 :=
    LinearPMap.mem_graph_snd_inj' g hforward hp (hU p.1)
  have hinverse : Vi p.2 = y := by
    calc
      Vi p.2 = Vi (V y) := congrArg Vi houtput.symm
      _ = y := hV y
  simpa only [hinverse] using hy

#print axioms partialGraph_reverse_of_domain_forward
end
end FCP.M4F9H4C2A1GenericPartialGraphReverse
