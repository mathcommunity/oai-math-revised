import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4C2CExactNativeChargeNaturalDomain

/-!
BFSS M4F9 H4C2D — actual sixteen native Hilbert supercharge actions
intertwine on their EXACT natural domains. Depends on qualified H4C2B
two-sided graph equivalence and H4C2C exact natural domains. The
independent J-free E2 charge and source AY charge remain unchanged.

No adjoint, Hamiltonian operator domain, or spectral assertion.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H4C2DExactNativeChargeAction
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.M4F9H2APhysicalHilbertOutputUnitary
open FCP.M4F9H2CActualE2NativeHilbertChargeColumn
open FCP.M4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
  theta α A * theta β B + theta β B * theta α A =
    (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
variable (hHermitian : ∀ α A, (theta α A).IsSymmetric)
variable (color : ColorIndex 2 → ColorMatrix 2)
variable (gamma : SpaceIndex → GammaMatrix)
variable (J : E ≃ₗᵢ[ℂ] Fermion 2)
variable (hColor : color = pairedAlgebraData.color)
variable (hGamma : gamma = pairedAlgebraData.gamma)
variable (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
include color gamma hColor hGamma

/-- The ACTUAL source-defined AY native charge acts on the unitary
image of every independent J-free E2 natural-domain vector exactly
as the Hilbert-output unitary transports the independent charge. -/
theorem nativePhysicalCharge_action_intertwine
    (u : independentPhysicalSpace theta hCAR hHermitian)
    (hu : u ∈ (independentActualE2NativeHilbertChargeColumn
      theta hCAR hHermitian color gamma).domain) :
    let U := independentPhysicalUnitary theta hCAR hHermitian J hJ
    let V := independentPhysicalHilbertOutputUnitary theta hCAR hHermitian J hJ
    let f := independentActualE2NativeHilbertChargeColumn
      theta hCAR hHermitian color gamma
    let g := pairedOriginalNativePhysicalHilbertChargeColumn
    V (f ⟨u,hu⟩) =
      g ⟨U u,
        (FCP.M4F9H4C2CExactNativeChargeNaturalDomain.nativeIndependentDomain_mem_iff_sourceDomain
          theta hCAR hHermitian color gamma J hColor hGamma hJ u).mp hu⟩ := by
  dsimp only
  let U := independentPhysicalUnitary theta hCAR hHermitian J hJ
  let V := independentPhysicalHilbertOutputUnitary theta hCAR hHermitian J hJ
  let f := independentActualE2NativeHilbertChargeColumn
    theta hCAR hHermitian color gamma
  let g := pairedOriginalNativePhysicalHilbertChargeColumn
  have hs : U u ∈ g.domain :=
    (FCP.M4F9H4C2CExactNativeChargeNaturalDomain.nativeIndependentDomain_mem_iff_sourceDomain
      theta hCAR hHermitian color gamma J hColor hGamma hJ u).mp hu
  have hf : (u, f ⟨u,hu⟩) ∈ f.graph := f.mem_graph ⟨u,hu⟩
  have hforward : (U u, V (f ⟨u,hu⟩)) ∈ g.graph :=
    (FCP.M4F9H4C2BExactNativeChargeGraphConjugacy.nativeIndependentGraph_mem_iff_sourceGraph
      theta hCAR hHermitian color gamma J hColor hGamma hJ
      (u,f ⟨u,hu⟩)).mp hf
  have hg : (U u, g ⟨U u,hs⟩) ∈ g.graph := g.mem_graph ⟨U u,hs⟩
  exact g.mem_graph_snd_inj hforward hg rfl

#print axioms nativePhysicalCharge_action_intertwine
end
end FCP.M4F9H4C2DExactNativeChargeAction
