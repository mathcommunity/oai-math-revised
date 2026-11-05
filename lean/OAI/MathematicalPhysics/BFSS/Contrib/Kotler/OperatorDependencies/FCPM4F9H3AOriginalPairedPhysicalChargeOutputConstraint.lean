import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H2D2BNativeHilbertE2ClosedGraph
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8BFOriginalSourceGraphAndPairedHamiltonianProbe

/-!
M4F9 H3A — Original paired-source AY physical Hilbert charge actually
has all sixteen outputs in the genuine original pairedGaugeData physical
Hilbert space, conditional only on the explicit original independent
Majorana/fiber matching witness.

Critically, original AY has OUTPUT PiLp2 of full L², whereas the
independent E2 operator has PiLp2 of *physical* L². Do not assume
they are the same codomain or silently claim a surjective unitary onto
the original full L² output. Prove the exact output constraint by the
original BF source graph crosswalk and independent DE4 named graph
identity, preserving both independently constructed operators.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H3AOriginalPairedPhysicalChargeOutputConstraint
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.IndependentSmoothSupercharge
open FCP.IndependentFullL2GaugeTransport
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open FCP.BFSSSU2PhysicalDomainL6H5E8BF
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))
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

-- The DE4 original/independent source matching witnesses are essential
-- theorem hypotheses even though the source-only conclusion does not name them.
include theta hCAR hHermitian color gamma J hColor hGamma hJ

/-- Each output of the ACTUAL original AY paired gauge-minimal
physical Hilbert charge belongs to the original physical subspace.
This theorem uses named DE4 graph image, not an unproved output
invariance postulate, and does not redefine AY's original codomain. -/
theorem pairedOriginalMinimalPhysicalHilbertChargeGraph_outputs_physical
    (p : pairedGaugeData.physicalSpace ×
      PiLp 2 (fun _ : SpinIndex => FullL2 2))
    (hp : p ∈ originalMinimalPhysicalHilbertChargeGraph
      pairedAlgebraData pairedGaugeData) :
    ∀ α : SpinIndex, p.2 α ∈ pairedGaugeData.physicalSpace := by
  have hs :
      ((p.1 : FullL2 2), originalMinimalHilbertOutputEquiv p.2) ∈
        (pairedGaugeData.deformedModelGraph 1 0 :
          Set (FullL2 2 × (SpinIndex → FullL2 2))) :=
    (originalMinimalPhysicalHilbertChargeGraph_mem_source_iff
      pairedAlgebraData pairedGaugeData p).mp hp
  rw [FCP.M4F8OriginalNamedFullPhysicalGraphDE4.pairedSourceNamedClosedGraph_eq_actualIndependentFullPhysicalGraph_image
    color gamma theta hCAR hHermitian J hColor hGamma hJ] at hs
  rcases hs with ⟨_, ⟨r, hr, rfl⟩, htransport⟩
  intro α
  have hy :
      (r.2 : SpinIndex → Lp E 2 μ) ∈
        Submodule.pi Set.univ
          (fun (_ : SpinIndex) =>
            independentPhysicalSpace theta hCAR hHermitian) :=
    r.2.property
  have hphysical :
      ((r.2 : SpinIndex → Lp E 2 μ) α) ∈
        independentPhysicalSpace theta hCAR hHermitian :=
    (Submodule.mem_pi).mp hy α (Set.mem_univ α)
  have hsource :
      fiberTransport J ((r.2 : SpinIndex → Lp E 2 μ) α) ∈
        pairedGaugeData.physicalSpace :=
    (independentPhysicalSpace_iff_source
      theta hCAR hHermitian J hJ _).mp hphysical
  have heq :
      fiberTransport J ((r.2 : SpinIndex → Lp E 2 μ) α) = p.2 α := by
    have h := congrArg
      (fun z : FullL2 2 × (SpinIndex → FullL2 2) => z.2 α) htransport
    exact h
  exact heq ▸ hsource

#print axioms pairedOriginalMinimalPhysicalHilbertChargeGraph_outputs_physical

end
end FCP.M4F9H3AOriginalPairedPhysicalChargeOutputConstraint
