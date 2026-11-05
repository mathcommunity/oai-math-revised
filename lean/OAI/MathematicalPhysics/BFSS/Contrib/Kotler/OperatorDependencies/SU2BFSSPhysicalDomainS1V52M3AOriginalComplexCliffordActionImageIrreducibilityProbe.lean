import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52M2OriginalComplexifiedCliffordFockRepresentationProbe

/-!
S1V52-M3A — IRREDUCIBILITY of the actual ORIGINAL complexified
48-Clifford action on genuine original 24-mode Fock space.

This is the first source-exact prerequisite for M3 surjectivity
of originalComplexCliffordFockAlgHom onto the FULL complex
Fock endomorphism algebra. We use the qualified exact M2 generator
identity and G1A original paired 48-theta irreducibility.
The source gamma axis uses the exact sqrt(2) normalization;
no unnamed alternate action or independent abstract Fock module.

This theorem is NOT the still-open M3 surjectivity and does NOT
construct the nonzero independent manuscript intertwiner.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52M3A
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L9E2
open FCP.BFSSS1V52L9E4
open FCP.BFSSS1V52M2
open scoped TensorProduct

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Any COMPLEX Fock submodule invariant under the ENTIRE original
complexified source Clifford representation has no proper,
nontrivial invariant subspaces. Actual 48-source operators only. -/
theorem originalComplexCliffordFock_image_irreducible
    (W : Submodule ℂ (Fermion 2))
    (hW : ∀ x : CliffordAlgebra (Q.baseChange ℂ),
      ∀ w ∈ W, originalComplexCliffordFockAlgHom x w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  apply pairedTheta_irreducible W
  intro α A w hw
  let q : RealSpinBlock := spinPairEquiv α
  let v : Source48Vector := sourceBlockColorAxis q A
  have hgamma :
      originalComplexCliffordFockAlgHom
        (CliffordAlgebra.ι (Q.baseChange ℂ) (1 ⊗ₜ[ℝ] v)) =
      originalNormalizedFockMajorana q A :=
    (originalComplexCliffordFockAlgHom_generator v).trans
      (originalFockGammaRealLinear_sourceAxis q A)
  have hnorm : (originalNormalizedFockMajorana q A) w ∈ W := by
    rw [← hgamma]
    exact hW _ w hw
  have hq : spinPairEquiv.symm q = α :=
    spinPairEquiv.symm_apply_apply α
  change ((↑(Real.sqrt 2) : ℂ) • pairedTheta
    (spinPairEquiv.symm q) A) w ∈ W at hnorm
  rw [hq] at hnorm
  have hcReal : Real.sqrt (2 : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  have hc : (↑(Real.sqrt 2) : ℂ) ≠ 0 := by
    exact_mod_cast hcReal
  have hn : (↑(Real.sqrt 2) : ℂ) • (pairedTheta α A w) ∈ W := by
    simpa only [ContinuousLinearMap.smul_apply] using hnorm
  have hinv := W.smul_mem ((↑(Real.sqrt 2) : ℂ)⁻¹) hn
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hinv

#print axioms originalComplexCliffordFock_image_irreducible

end
end FCP.BFSSS1V52M3A
