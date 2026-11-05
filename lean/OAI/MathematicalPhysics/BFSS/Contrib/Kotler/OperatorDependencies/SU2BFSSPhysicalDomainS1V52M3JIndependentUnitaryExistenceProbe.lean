import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52M3IOriginalComplexCliffordFockAlgebraEquivProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1ASchurScalarCommutantProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM3LUnitaryCliffordModuleExistence

/-!
SOURCE-EXACT ADAPTER CANDIDATE -- NOT LOCALLY COMPILED.

Required accepted inputs: M3I blob 300df1d7c886b636f2cfc206ac36f8b97f91d4b4,
M2 blob fa67dfde6cb6a21a97180797bdf5e917e0b417d2 and original G1A,
S1A algebraic commutant blob fd5f9e0f3d36a52e3a0222116022a11a83c387d7.
This is compiled afresh from its original pinned source, with no H5E8AC cache.
Lean 4.34.1 / Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.

The four generic helper modules have separately passed local compilation
and permitted-axiom checks. This adapter requires qualified original
source oleans; no substitute modules should be used to test it.

No independent action or nonzero intertwiner is assumed. E and its
actual manuscript theta operators stay arbitrary. The conclusion only
identifies the finite fermionic module and its labeled generators.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.BFSSS1V52M3JIndependent
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSS1V0 FCP.BFSSS1V5
open FCP.BFSSS1V52L9E2 FCP.BFSSS1V52L9E4 FCP.BFSSS1V52M2
open FCP.BFSSS1V52M3I
open scoped TensorProduct

/-- The exact already-used source block/color -> manuscript labels,
with the existing spinPairEquiv and sourceBlockColorEquiv. -/
def sourceToManuscriptLabel : SourceLabel ≃ (SpinIndex × ColorIndex 2) :=
  sourceBlockColorEquiv.symm.trans
    (Equiv.prodCongr spinPairEquiv.symm (Equiv.refl (Fin 3)))

private abbrev V := Fermion 2
private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev A := CliffordAlgebra (Q.baseChange ℂ)

theorem independent_original_generator_unitary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Nontrivial E]
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hHermitian : ∀ α C, (theta α C).IsSymmetric)
    (hCAR : ∀ α β C D,
      theta α C * theta β D + theta β D * theta α C =
        (if α = β ∧ C = D then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
    (hirr : ∀ W : Submodule ℂ E,
      (∀ α C, ∀ w ∈ W, theta α C w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ J : E ≃ₗᵢ[ℂ] Fermion 2,
      ∀ (α : SpinIndex) (C : ColorIndex 2) (w : E),
        J (theta α C w) = pairedTheta α C (J w) := by
  let e := sourceToManuscriptLabel
  let source : SourceLabel → Module.End ℂ V :=
    fun p => (pairedTheta (e p).1 (e p).2).toLinearMap
  let target : SourceLabel → Module.End ℂ E :=
    fun p => theta (e p).1 (e p).2
  let Phi : A ≃ₐ[ℂ] Module.End ℂ V :=
    originalComplexCliffordFockAlgEquiv.trans
      (Module.End.toContinuousLinearMap V).symm
  have hPhi : ∀ p : SourceLabel,
      Phi (CliffordAlgebra.ι _ ((1 : ℂ) ⊗ₜ[ℝ] (Pi.single p (1 : ℝ)))) =
        (Real.sqrt 2 : ℂ) • source p := by
    intro p
    let q := sourceBlockColorEquiv.symm p
    let v : Source48Vector := sourceBlockColorAxis q.1 q.2
    have hv : v = Pi.single p (1 : ℝ) := by
      dsimp only [v, sourceBlockColorAxis, sourceBlockColorLabel, q]
      rw [sourceBlockColorEquiv.apply_symm_apply]
    have hg : originalComplexCliffordFockAlgEquiv
        (CliffordAlgebra.ι _ ((1 : ℂ) ⊗ₜ[ℝ] v)) =
          originalNormalizedFockMajorana q.1 q.2 := by
      rw [originalComplexCliffordFockAlgEquiv_apply,
        originalComplexCliffordFockAlgHom_generator]
      exact originalFockGammaRealLinear_sourceAxis q.1 q.2
    change (Module.End.toContinuousLinearMap V).symm
      (originalComplexCliffordFockAlgEquiv
        (CliffordAlgebra.ι _ ((1 : ℂ) ⊗ₜ[ℝ] (Pi.single p (1 : ℝ))))) = _
    rw [← hv, hg]
    rfl
  have hsource : ∀ p, (source p).IsSymmetric := by
    intro p
    exact (pairedTheta_selfAdjoint (e p).1 (e p).2).isSymmetric
  have hscalar : ∀ G : Module.End ℂ V,
      (∀ p w, G (source p w) = source p (G w)) →
        ∃ c : ℂ, G = c • (1 : Module.End ℂ V) := by
    intro G hG
    have hcomm : ∀ α C w, G (pairedTheta α C w) = pairedTheta α C (G w) := by
      intro α C w
      have h := hG (e.symm (α, C)) w
      simpa only [source, e.apply_symm_apply, ContinuousLinearMap.coe_coe] using h
    obtain ⟨c, hc⟩ :=
      FCP.BFSSSU2PhysicalDomainS1A.pairedTheta_commutant_scalar G hcomm
    refine ⟨c, ?_⟩
    apply LinearMap.ext
    intro w
    simpa only [LinearMap.smul_apply, Module.End.one_apply] using hc w
  have htargetCAR : ∀ p q,
      target p * target q + target q * target p =
        (if p = q then (1 : ℂ) else 0) • (1 : Module.End ℂ E) := by
    intro p q
    have heq : ((e p).1 = (e q).1 ∧ (e p).2 = (e q).2) ↔ p = q := by
      constructor
      · rintro ⟨h1, h2⟩
        exact e.injective (Prod.ext h1 h2)
      · intro h
        subst q
        exact ⟨rfl, rfl⟩
    simpa only [target, heq] using hCAR (e p).1 (e q).1 (e p).2 (e q).2
  have htarget : ∀ p, (target p).IsSymmetric :=
    fun p => hHermitian (e p).1 (e p).2
  have htargetIrr : ∀ W : Submodule ℂ E,
      (∀ p, ∀ w ∈ W, target p w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    apply hirr W
    intro α C w hw
    have h := hW (e.symm (α, C)) w hw
    simpa only [target, e.apply_symm_apply] using h
  obtain ⟨U, hU⟩ := FCP.IndependentM3L.exists_unitary_deltaOne
    Phi source hPhi hsource hscalar target htargetCAR htarget htargetIrr
  refine ⟨U.symm, ?_⟩
  intro α C w
  have h : U (pairedTheta α C (U.symm w)) = theta α C w := by
    simpa only [source, target, e.apply_symm_apply, U.apply_symm_apply,
      ContinuousLinearMap.coe_coe] using
      hU (e.symm (α, C)) (U.symm w)
  have hh := congrArg U.symm h
  simpa only [U.symm_apply_apply] using hh.symm

#print axioms sourceToManuscriptLabel
#print axioms independent_original_generator_unitary

end
end FCP.BFSSS1V52M3JIndependent
