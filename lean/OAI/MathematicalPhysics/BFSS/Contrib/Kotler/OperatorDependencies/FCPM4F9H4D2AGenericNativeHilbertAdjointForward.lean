import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4D1OriginalNativeHilbertChargeDomainDense
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
BFSS M4F9 H4D2A — source-free densely-defined partial Hilbert
operator ADJOINT covariance under ACTUAL Hilbert unitaries.
Two distinct charge operators f, g (NOT defined by transport).
The hypotheses spell out exact domain transport, charge action
transport, and density on both sides. Then their true Hilbert
adjoints have transported domain membership and action.

This theorem is a reusable generic forward adjoint graph inclusion.
Reverse and actual BFSS specialization will be separately gated.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H4D2AGenericNativeHilbertAdjointForward
noncomputable section

variable {E F E' F' : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
variable [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

/-- For genuinely densely defined partial complex Hilbert operators
with both entire natural domains transported by a physical unitary
and corresponding actions transported by an output unitary, the
Hilbert adjoint domains/actions transport forward as well. -/
theorem adjoint_forward_domain_action
    (f : E →ₗ.[ℂ] F) (g : E' →ₗ.[ℂ] F')
    (U : E ≃ₗᵢ[ℂ] E') (V : F ≃ₗᵢ[ℂ] F')
    (hfDense : Dense (f.domain : Set E))
    (hgDense : Dense (g.domain : Set E'))
    (hFwdDomain : ∀ x : E, x ∈ f.domain → U x ∈ g.domain)
    (hRevDomain : ∀ z : E', z ∈ g.domain → U.symm z ∈ f.domain)
    (hAct : ∀ x : f.domain,
      V (f x) = g ⟨U (x : E), hFwdDomain (x : E) x.property⟩)
    (y : F) (hy : y ∈ f.adjoint.domain) :
    ∃ (hVy : V y ∈ g.adjoint.domain),
      g.adjoint ⟨V y, hVy⟩ = U (f.adjoint ⟨y, hy⟩) := by
  let A : E := f.adjoint ⟨y, hy⟩
  have hPair (z : g.domain) :
      inner ℂ (U A) (z : E') = inner ℂ (V y) (g z) := by
    let x : f.domain :=
      ⟨U.symm (z : E'), hRevDomain (z : E') z.property⟩
    have hUx : U (x : E) = (z : E') :=
      U.apply_symm_apply (z : E')
    have hAction : V (f x) = g z := by
      simpa only [hUx] using hAct x
    calc
      inner ℂ (U A) (z : E') =
          inner ℂ (U A) (U (x : E)) := by rw [hUx]
      _ = inner ℂ A (x : E) := U.inner_map_map A (x : E)
      _ = inner ℂ y (f x) :=
        LinearPMap.adjoint_isFormalAdjoint hfDense ⟨y, hy⟩ x
      _ = inner ℂ (V y) (V (f x)) :=
        (V.inner_map_map y (f x)).symm
      _ = inner ℂ (V y) (g z) := by rw [hAction]
  have hVy : V y ∈ g.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists (V y) ⟨U A, hPair⟩
  refine ⟨hVy, ?_⟩
  exact LinearPMap.adjoint_apply_eq hgDense ⟨V y, hVy⟩ hPair

#print axioms adjoint_forward_domain_action
end
end FCP.M4F9H4D2AGenericNativeHilbertAdjointForward
