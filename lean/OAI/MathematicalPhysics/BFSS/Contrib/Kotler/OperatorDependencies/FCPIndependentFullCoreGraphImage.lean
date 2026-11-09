import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentFullCoreGraph
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentInvariantSmoothEquiv

/-!
M4F4: the source original unrestricted sixteen-charge smooth-core graph
is the exact image of the independently constructed core graph under
the genuine 17-component L² fiber transport.

The additional direction is not assumed: it comes from the already
accepted two-sided smooth TestFunction equivalence (M4D2), the
independent charge column (M4F2), and the one-way graph theorem (M4F3).

All statements are about UNRESTRICTED smooth-core graphs. This file
does not infer closed graphs, gauge-invariant physical restrictions,
Hamiltonian equality or spectral results.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.IndependentSmoothSupercharge
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.IndependentSmoothCore
open FCP.IndependentFullL2GaugeTransport
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

private abbrev μ := (volume : Measure (Boson 2))

/-- Every original smooth-core graph point comes from a genuine
independent smooth-core graph point; witness is obtained by inverting
the already verified TestFunction fiber equivalence. -/
theorem sourceFullCoreGraph_transport_exists_independent
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (q : FullL2 2 × (SpinIndex → FullL2 2))
    (hq : q ∈ pairedAlgebraData.fullCoreGraph) :
    ∃ p : Lp E 2 μ × (SpinIndex → Lp E 2 μ),
      p ∈ independentFullCoreGraph color gamma theta ∧
        (fiberTransport J p.1,
          fun α : SpinIndex => fiberTransport J (p.2 α)) = q := by
  rcases hq with ⟨g, rfl⟩
  let f : IndependentTestCore E := (independentSmoothLinearEquiv J).symm g
  have hf : independentSmoothTransport J f = g := by
    change (independentSmoothLinearEquiv J)
      ((independentSmoothLinearEquiv J).symm g) = g
    exact (independentSmoothLinearEquiv J).apply_symm_apply g
  refine ⟨(independentCoreToL2.prod
      (independentChargeVector color gamma theta)) f, ?_, ?_⟩
  · exact ⟨f, rfl⟩
  · change (fiberTransport J (independentCoreToL2 f),
        fun α : SpinIndex =>
          fiberTransport J (independentChargeVector color gamma theta f α)) =
        (coreToL2 g, pairedAlgebraData.chargeVector g)
    apply Prod.ext
    · calc
        fiberTransport J (independentCoreToL2 f) =
            coreToL2 (independentSmoothTransport J f) :=
          independentSmoothTransport_coreToL2 J f
        _ = coreToL2 g := congrArg coreToL2 hf
    · calc
        (fun α : SpinIndex =>
          fiberTransport J (independentChargeVector color gamma theta f α)) =
            pairedAlgebraData.chargeVector (independentSmoothTransport J f) :=
          independentChargeVector_all_components_intertwining
            color gamma theta J hColor hGamma hJ f
        _ = pairedAlgebraData.chargeVector g :=
          congrArg pairedAlgebraData.chargeVector hf

/-- Original pinned full smooth-core graph equals the set-theoretic
image of the genuinely independent smooth-core graph under the
componentwise 17-slot transport. No closure claim is present. -/
theorem sourceFullCoreGraph_eq_independent_image
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w)) :
    (pairedAlgebraData.fullCoreGraph : Set
      (FullL2 2 × (SpinIndex → FullL2 2))) =
    (fun p : Lp E 2 μ × (SpinIndex → Lp E 2 μ) =>
      (fiberTransport J p.1,
        fun α : SpinIndex => fiberTransport J (p.2 α))) ''
      (independentFullCoreGraph color gamma theta : Set _) := by
  ext q
  constructor
  · intro hq
    exact sourceFullCoreGraph_transport_exists_independent
      color gamma theta J hColor hGamma hJ q hq
  · rintro ⟨p, hp, rfl⟩
    exact independentFullCoreGraph_transport_mem_source
      color gamma theta J hColor hGamma hJ p hp

#print axioms sourceFullCoreGraph_transport_exists_independent
#print axioms sourceFullCoreGraph_eq_independent_image

end
end FCP.IndependentSmoothSupercharge
