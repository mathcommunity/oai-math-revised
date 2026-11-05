import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4D2AGenericNativeHilbertAdjointForward

/-!
BFSS M4F9 H4D2B — reverse generic Hilbert adjoint
domain/action covariance for actual densely-defined LinearPMap
pairs. Derive by the STRICTLY ACCEPTED H4D2A forward theorem
swapping f, g, input unitary U.symm, output unitary V.symm.
No independent charge is defined through the desired result.
No BFSS actual source specialization is claimed here.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H4D2BGenericNativeHilbertAdjointReverse
noncomputable section

variable {E F E' F' : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
variable [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

/-- The genuine reverse Hilbert-adjoint domain and action from source
to independent operators, under the SAME two-way domain and actual
forward charge-action hypotheses as the qualified forward result. -/
theorem adjoint_reverse_domain_action
    (f : E →ₗ.[ℂ] F) (g : E' →ₗ.[ℂ] F')
    (U : E ≃ₗᵢ[ℂ] E') (V : F ≃ₗᵢ[ℂ] F')
    (hfDense : Dense (f.domain : Set E))
    (hgDense : Dense (g.domain : Set E'))
    (hFwdDomain : ∀ x : E, x ∈ f.domain → U x ∈ g.domain)
    (hRevDomain : ∀ z : E', z ∈ g.domain → U.symm z ∈ f.domain)
    (hAct : ∀ x : f.domain,
      V (f x) = g ⟨U (x : E), hFwdDomain (x : E) x.property⟩)
    (y : F') (hy : y ∈ g.adjoint.domain) :
    ∃ (hVy : V.symm y ∈ f.adjoint.domain),
      f.adjoint ⟨V.symm y, hVy⟩ = U.symm (g.adjoint ⟨y, hy⟩) := by
  have hActRev (z : g.domain) :
      V.symm (g z) =
        f ⟨U.symm (z : E'), hRevDomain (z : E') z.property⟩ := by
    let x : f.domain :=
      ⟨U.symm (z : E'), hRevDomain (z : E') z.property⟩
    have hUx : U (x : E) = (z : E') :=
      U.apply_symm_apply (z : E')
    have hSource : V (f x) = g z := by
      simpa only [hUx] using hAct x
    calc
      V.symm (g z) = V.symm (V (f x)) :=
        congrArg V.symm hSource.symm
      _ = f x := V.symm_apply_apply (f x)
  exact FCP.M4F9H4D2AGenericNativeHilbertAdjointForward.adjoint_forward_domain_action
    g f U.symm V.symm hgDense hfDense hRevDomain hFwdDomain
    hActRev y hy

#print axioms adjoint_reverse_domain_action
end
end FCP.M4F9H4D2BGenericNativeHilbertAdjointReverse
