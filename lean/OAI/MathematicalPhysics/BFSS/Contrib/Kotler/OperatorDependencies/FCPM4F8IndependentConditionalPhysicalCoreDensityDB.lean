import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F8IndependentInvariantCoreL2ImageDA

/-!
M4F8 DB — conditional genuine independent physical smooth-core
Hilbert-norm density, transported by the actual full-L2 fiber unitary.

This PROSPECTIVE leaf is deliberately conditional on the exact source
gauge-invariant smooth-core L2 closure equality. It does not import
unavailable D2B10C Haar .olean files or assert source Haar closure for
free. Neither independent core nor physical subspace is defined by
transport; both come from their original independent constructions.

DA supplies actual two-sided invariant-core image equality. M4C3
supplies the literal physical-space iff and original physical
closedness. Density here is Hilbert norm closure in the ambient
independent L2, NOT E2 graph-norm density or operator-domain density.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F8IndependentConditionalPhysicalCoreDensityDB
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentSmoothCore
open FCP.IndependentPhysicalSpace
open FCP.IndependentFullL2GaugeTransport
open FCP.M4F8IndependentInvariantCoreL2ImageDA
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))

/-- Precisely conditional Hilbert-norm density of the ACTUAL
independent gauge-invariant smooth L2 image in the J-free
independent physical Hilbert submodule.

The source closure premise is the exact statement separately
proved by the historical Haar D2B10C Gate #47. Its proof is
NOT assumed imported or silently reconstructed here. -/
theorem independentInvariantCoreL2_closure_eq_physical_of_source
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (hsource :
      closure (LinearMap.range
        (coreToL2.comp pairedGaugeData.invariantCore.subtype) :
          Set (FullL2 2)) =
        (pairedGaugeData.physicalSpace : Set (FullL2 2))) :
    closure (LinearMap.range
      (independentInvariantCoreToL2 theta hCAR hHermitian) :
        Set (Lp E 2 μ)) =
      (independentPhysicalSpace theta hCAR hHermitian :
        Set (Lp E 2 μ)) := by
  let F : Lp E 2 μ ≃ₗᵢ[ℂ] FullL2 2 := fiberTransportUnitary J
  let S : Set (Lp E 2 μ) :=
    LinearMap.range (independentInvariantCoreToL2 theta hCAR hHermitian)
  let T : Set (FullL2 2) :=
    LinearMap.range (coreToL2.comp pairedGaugeData.invariantCore.subtype)
  have himages : F '' S = T := by
    exact independentInvariantCoreToL2_unitary_image_eq_source
      theta hCAR hHermitian J hJ
  have hphys : (independentPhysicalSpace theta hCAR hHermitian :
      Set (Lp E 2 μ)) =
      F ⁻¹' (pairedGaugeData.physicalSpace : Set (FullL2 2)) := by
    ext v
    change v ∈ independentPhysicalSpace theta hCAR hHermitian ↔
      fiberTransport J v ∈ pairedGaugeData.physicalSpace
    exact independentPhysicalSpace_iff_source
      theta hCAR hHermitian J hJ v
  have hphysClosed :
      IsClosed (independentPhysicalSpace theta hCAR hHermitian :
        Set (Lp E 2 μ)) := by
    rw [hphys]
    exact pairedGaugeData.physicalSpace_closed.preimage F.continuous
  have hcorePhysical : S ⊆
      (independentPhysicalSpace theta hCAR hHermitian :
        Set (Lp E 2 μ)) := by
    rintro v ⟨f, rfl⟩
    change independentCoreToL2 f.val ∈
      independentPhysicalSpace theta hCAR hHermitian
    exact f.prop
  have hclosedTransport :
      IsClosed {w : FullL2 2 | F.symm w ∈ closure S} :=
    isClosed_closure.preimage F.symm.continuous
  have hsourceCoreSubset :
      T ⊆ {w : FullL2 2 | F.symm w ∈ closure S} := by
    intro w hw
    rw [← himages] at hw
    rcases hw with ⟨v, hv, rfl⟩
    change F.symm (F v) ∈ closure S
    simpa only [F.symm_apply_apply] using (subset_closure hv)
  have hsourcePhysicalSubset :
      (pairedGaugeData.physicalSpace : Set (FullL2 2)) ⊆
        {w : FullL2 2 | F.symm w ∈ closure S} := by
    rw [← hsource]
    exact closure_minimal hsourceCoreSubset hclosedTransport
  apply Set.Subset.antisymm
  · exact closure_minimal hcorePhysical hphysClosed
  · intro v hv
    have hvsource : F v ∈
        (pairedGaugeData.physicalSpace : Set (FullL2 2)) := by
      rw [hphys] at hv
      exact hv
    have hcl := hsourcePhysicalSubset hvsource
    change F.symm (F v) ∈ closure S at hcl
    simpa only [F.symm_apply_apply] using hcl

#print axioms independentInvariantCoreL2_closure_eq_physical_of_source

end
end FCP.M4F8IndependentConditionalPhysicalCoreDensityDB
