import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7NamedConditionalPhysicalOutputBridgeE7L

/-!
M4F7 E7M — UNCONDITIONAL physical-output inclusion for the
exact original independently constructed literal restricted
smooth-core closed graph, under the source-exact CAR, Hermitian,
color/gamma and fiber intertwining hypotheses.

This is the result of strictly accepted E7L after discharging
its two analytic premises:
  hP: genuinely independent SU(2) physical L² is CLOSED (E6);
  hQ: each actual independent smooth-core charge output lies in
      that physical submodule (E7A and E7K2 exact output identity).

The closed graph is the accepted E7D original J-free source graph.
The output predicate is the accepted E7I original J-free physical
sixteen-output predicate. J is a hypothesis witnessing source
representation equality; it is not part of either definition.

This leaf does NOT name the actual E2 LinearPMap.graph; final
actual closed-operator physical-output membership is separately
reserved for E7N through accepted E3 graph equality. Neither
domain density nor Hamiltonian or spectral claims follow.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F7IndependentLiteralClosedPhysicalOutputsE7M
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentSmoothCore
open FCP.IndependentSmoothSupercharge
open FCP.IndependentPhysicalSpace
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))

/-- Genuine original J-free independent literal restricted CLOSED
sixteen-charge graph has physical output in every coordinate,
discharging the two conditional E7L analytic hypotheses from
strictly accepted original SU(2) source theorems. -/
theorem independentLiteralRestrictedClosedGraph_subset_allPhysicalOutputs
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w)) :
    FCP.M4F7OpaqueLiteralGraphInterfaceE7D.literalRestrictedClosedGraphSet
        color gamma theta hCAR hHermitian ⊆
      FCP.M4F7IndependentPhysicalOutputPredicateE7I.independentAllSixteenOutputsPhysicalSet
        theta hCAR hHermitian := by
  have hP : IsClosed
      ((independentPhysicalSpace theta hCAR hHermitian :
        Submodule ℂ (Lp E 2 μ)) : Set (Lp E 2 μ)) :=
    FCP.M4F7IndependentClosedChargePhysicalInputE6.independentPhysicalSpace_isClosed
      theta hCAR hHermitian J hJ
  have hQ :
      ∀ (f : independentInvariantCore theta hCAR hHermitian)
        (α : SpinIndex),
        (FCP.M4F7IndependentNamedSmoothGraphMapsE7K.independentInvariantCoreOutputMap
          color gamma theta hCAR hHermitian f) α ∈
          independentPhysicalSpace theta hCAR hHermitian := by
    intro f α
    have hOriginal :=
      FCP.M4F7IndependentChargeOutputTypedE7A.independentChargeVector_comp_invariantCore_output_physical
        color gamma theta hCAR hHermitian J hColor hGamma hJ f α
    simpa only [FCP.M4F7NamedSmoothGraphIdentityE7K2.independentInvariantCoreOutputMap_eq]
      using hOriginal
  exact FCP.M4F7NamedConditionalPhysicalOutputBridgeE7L.originalNamedClosedGraph_subset_nativeSixteenPhysicalOutputs_of_core
    color gamma theta hCAR hHermitian hP hQ

#print axioms independentLiteralRestrictedClosedGraph_subset_allPhysicalOutputs

end
end FCP.M4F7IndependentLiteralClosedPhysicalOutputsE7M
