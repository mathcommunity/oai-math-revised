import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM3JRankOneModuleExistence
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM3JIndependentCliffordAction
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM3KHilbertNormalization
import Mathlib.Tactic.NormNum

/-!
End-to-end independent-module existence from actual normalized Hermitian
CAR operators. The independent action and intertwiner are constructed.
The source equivalence, generator identities and source commutant are
explicit inputs, intended for the already accepted original Fock results.
No Clifford star occurs in the proof.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace FCP.IndependentM3L
noncomputable section

open FCP.IndependentM3J FCP.IndependentM3JAction FCP.IndependentM3K
open scoped TensorProduct

variable {V E I : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ E]
variable [Nontrivial V] [Nontrivial E]

private abbrev A := CliffordAlgebra
  ((coordinateQuadratic (R := ℝ) (I := I)).baseChange ℂ)

/-- An independent nonzero irreducible Hermitian CAR family admits a
unitary generator-preserving equivalence with the specified full source
Clifford representation. Its Clifford action is constructed internally. -/
theorem exists_unitary_of_fullCliffordEquiv
    (Phi : A (I := I) ≃ₐ[ℂ] Module.End ℂ V)
    (source : I → Module.End ℂ V)
    (hPhi : ∀ i, Phi (CliffordAlgebra.ι _
      ((1 : ℂ) ⊗ₜ[ℝ] (Pi.single i (1 : ℝ)))) = source i)
    (hsource : ∀ i, (source i).IsSymmetric)
    (hscalar : ∀ G : Module.End ℂ V,
      (∀ i v, G (source i v) = source i (G v)) →
        ∃ c : ℂ, G = c • (1 : Module.End ℂ V))
    (gamma : I → Module.End ℂ E)
    (hdiag : ∀ i, gamma i * gamma i = 1)
    (hanti : ∀ i j, i ≠ j → gamma i * gamma j + gamma j * gamma i = 0)
    (hgamma : ∀ i, (gamma i).IsSymmetric)
    (hirr : ∀ W : Submodule ℂ E,
      (∀ i, ∀ w ∈ W, gamma i w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ U : V ≃ₗᵢ[ℂ] E,
      ∀ i v, U (source i v) = gamma i (U v) := by
  let sigma : A (I := I) →ₐ[ℂ] Module.End ℂ E :=
    independentComplexCliffordAction (R := ℝ) (S := ℂ) gamma hdiag hanti
  have hsigma : ∀ i, sigma (CliffordAlgebra.ι _
      ((1 : ℂ) ⊗ₜ[ℝ] (Pi.single i (1 : ℝ)))) = gamma i := by
    intro i
    exact (independentComplexCliffordAction_generator gamma hdiag hanti
      (Pi.single i (1 : ℝ))).trans (independentGammaReal_axis gamma i)
  have hsirr : ∀ W : Submodule ℂ E,
      (∀ a : A (I := I), ∀ w ∈ W, sigma a w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    apply hirr W
    intro i w hw
    rw [← hsigma i]
    exact hW _ w hw
  obtain ⟨T, hT⟩ := exists_algebra_intertwining_equiv
    (Module.finBasis ℂ V) Phi sigma hsirr
  have hgen : ∀ i v, T (source i v) = gamma i (T v) := by
    intro i v
    rw [← hPhi i, ← hsigma i]
    exact hT _ v
  obtain ⟨U, r, hr, hscale, hU⟩ :=
    positive_normalization_of_intertwining_equiv
      source gamma hsource hgamma hscalar T hgen
  exact ⟨U, hU⟩

/-- Manuscript delta-one CAR, with the exact POSITIVE sqrt(2)
normalization. This theorem assumes neither a target Clifford action
nor a nonzero intertwiner. Both are constructed by the preceding proof. -/
theorem exists_unitary_deltaOne
    (Phi : A (I := I) ≃ₐ[ℂ] Module.End ℂ V)
    (source : I → Module.End ℂ V)
    (hPhi : ∀ i, Phi (CliffordAlgebra.ι _
      ((1 : ℂ) ⊗ₜ[ℝ] (Pi.single i (1 : ℝ)))) =
        (Real.sqrt 2 : ℂ) • source i)
    (hsource : ∀ i, (source i).IsSymmetric)
    (hscalar : ∀ G : Module.End ℂ V,
      (∀ i v, G (source i v) = source i (G v)) →
        ∃ c : ℂ, G = c • (1 : Module.End ℂ V))
    (theta : I → Module.End ℂ E)
    (hCAR : ∀ i j, theta i * theta j + theta j * theta i =
      (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
    (htheta : ∀ i, (theta i).IsSymmetric)
    (hirr : ∀ W : Submodule ℂ E,
      (∀ i, ∀ w ∈ W, theta i w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ U : V ≃ₗᵢ[ℂ] E,
      ∀ i v, U (source i v) = theta i (U v) := by
  let s : ℂ := ↑(Real.sqrt 2)
  have hs : s ≠ 0 := by
    dsimp [s]
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hs2 : s * s = (2 : ℂ) := by
    dsimp [s]
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hconj : starRingEnd ℂ s = s := by simp [s]
  let gamma : I → Module.End ℂ E := fun i => s • theta i
  let sourceGamma : I → Module.End ℂ V := fun i => s • source i
  have hdiag : ∀ i, gamma i * gamma i = 1 := by
    intro i
    have hc : theta i * theta i + theta i * theta i = 1 := by
      simpa using hCAR i i
    change (s • theta i) * (s • theta i) = 1
    rw [smul_mul_smul, hs2, two_smul]
    exact hc
  have hanti : ∀ i j, i ≠ j → gamma i * gamma j + gamma j * gamma i = 0 := by
    intro i j hij
    have hc := hCAR i j
    simp [hij] at hc
    change (s • theta i) * (s • theta j) + (s • theta j) * (s • theta i) = 0
    rw [smul_mul_smul, smul_mul_smul, ← smul_add, hc, smul_zero]
  have hsc : ∀ G : Module.End ℂ V,
      (∀ i v, G (sourceGamma i v) = sourceGamma i (G v)) →
        ∃ c : ℂ, G = c • (1 : Module.End ℂ V) := by
    intro G hG
    apply hscalar G
    intro i v
    have h : s • G (source i v) = s • source i (G v) := by
      simpa only [sourceGamma, LinearMap.smul_apply, map_smul] using hG i v
    have hh := congrArg (fun z : V => s⁻¹ • z) h
    simpa only [smul_smul, inv_mul_cancel₀ hs, one_smul] using hh
  have hgi : ∀ W : Submodule ℂ E,
      (∀ i, ∀ w ∈ W, gamma i w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    apply hirr W
    intro i w hw
    have h := W.smul_mem s⁻¹ (hW i w hw)
    simpa only [gamma, LinearMap.smul_apply, smul_smul,
      inv_mul_cancel₀ hs, one_smul] using h
  obtain ⟨U, hU⟩ := exists_unitary_of_fullCliffordEquiv
    Phi sourceGamma hPhi
    (fun i => LinearMap.IsSymmetric.smul hconj (hsource i)) hsc
    gamma hdiag hanti
    (fun i => LinearMap.IsSymmetric.smul hconj (htheta i)) hgi
  refine ⟨U, ?_⟩
  intro i v
  have h : s • U (source i v) = s • theta i (U v) := by
    simpa only [sourceGamma, gamma, LinearMap.smul_apply, map_smul] using hU i v
  have hh := congrArg (fun z : E => s⁻¹ • z) h
  simpa only [smul_smul, inv_mul_cancel₀ hs, one_smul] using hh

#print axioms exists_unitary_of_fullCliffordEquiv
#print axioms exists_unitary_deltaOne

end
end FCP.IndependentM3L
