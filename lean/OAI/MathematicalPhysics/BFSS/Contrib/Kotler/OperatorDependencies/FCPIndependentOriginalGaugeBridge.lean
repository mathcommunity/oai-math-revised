import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentOriginalCliffordBridge
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F18COriginalNativeFockSourceGaugeIdentificationProbe

/-!
SOURCE-EXACT RESEARCH CANDIDATE -- NOT LOCALLY TYPECHECKED.
Requires the actual qualified M3J AND F18C source .oleans together.

The independent action is evaluated on the genuine accepted native Spin
lift before selecting J. F18C is used only at the final comparison step.
Its strict acceptance was independently verified at run 39649964814.
This candidate establishes no unbounded-domain or spectral statements.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.IndependentOriginalGaugeBridge
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4B
open FCP.BFSSS1V0 FCP.BFSSS1V5
open FCP.BFSSS1V52L8E FCP.BFSSS1V52L9E1
open FCP.BFSSS1V52L9E5F15 FCP.BFSSS1V52L9E5F18C
open FCP.BFSSS1V52M3JIndependent
open FCP.BFSSSU2PhysicalDomainS1J
open FCP.IndependentOriginalCliffordBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
  theta α A * theta β B + theta β B * theta α A =
    (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
variable (hHermitian : ∀ α A, (theta α A).IsSymmetric)

/-- Genuine independent unitary gauge representation: universal independent
Clifford action restricted to the actual native sixteen-block Spin lift.
There is no J or original Fock gauge operator in this definition. -/
def independentOriginalGaugeHom : GaugeGroup 2 →* (E ≃ₗᵢ[ℂ] E) :=
  (independentOriginalSpinHom theta hCAR hHermitian).comp
    originalNativeSixteenSpinHom

/-- Independent all-48 real-generator covariance BEFORE using M3J.
The original source matrix, orientation and positive-i lift are retained. -/
theorem independent_original_gauge_real_covariance
    (g : GaugeGroup 2) (v : Source48Vector) (w : E) :
    independentOriginalGaugeHom theta hCAR hHermitian g
        (independentOriginalClifford theta hCAR (CliffordAlgebra.ι Q v) w) =
      independentOriginalClifford theta hCAR
        (CliffordAlgebra.ι Q ((sourceRealMajoranaMatrix g).mulVec v))
        (independentOriginalGaugeHom theta hCAR hHermitian g w) := by
  exact FCP.IndependentSpinRealization.spin_covariance_of_clifford_conjugation
    Q (independentOriginalClifford theta hCAR) (originalNativeSixteenSpinHom g)
    v ((sourceRealMajoranaMatrix g).mulVec v)
    (originalNativeSixteenSpinHom_clifford_generator_conj g v) w

/-- Every generator-preserving J intertwines the independently constructed
gauge representation with the ACTUAL original fermionGaugeLinearEquiv. -/
theorem independent_original_gauge_intertwining
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (g : GaugeGroup 2) (w : E) :
    J (independentOriginalGaugeHom theta hCAR hHermitian g w) =
      fermionGaugeLinearEquiv g (J w) := by
  have h := independent_original_clifford_intertwining theta hCAR J hJ
    ((originalNativeSixteenSpinHom g : spinGroup Q) : C) w
  change J (independentOriginalGaugeHom theta hCAR hHermitian g w) =
    originalNativeSixteenFockLinearEquivHom g (J w) at h
  have hs := congrArg
    (fun V : GaugeGroup 2 →* (Fermion 2 ≃ₗ[ℂ] Fermion 2) => V g (J w))
    originalNativeSixteenFock_sourceGaugeHom_identification
  exact h.trans hs

/-- Full source-exact invariant target, with independent gauge operators
defined above. Existence of J is furnished by accepted M3J, and its scalar
freedom introduces no phase in the conjugated group representation. -/
theorem exists_independent_original_gauge_unitary [Nontrivial E]
    (hirr : ∀ W : Submodule ℂ E,
      (∀ α A, ∀ w ∈ W, theta α A w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ J : E ≃ₗᵢ[ℂ] Fermion 2,
      (∀ α A w, J (theta α A w) = pairedTheta α A (J w)) ∧
      (∀ (g : GaugeGroup 2) (v : Fermion 2),
        J (independentOriginalGaugeHom theta hCAR hHermitian g (J.symm v)) =
          fermionGaugeLinearEquiv g v) := by
  obtain ⟨J, hJ⟩ := independent_original_generator_unitary theta hHermitian hCAR hirr
  refine ⟨J, hJ, ?_⟩
  intro g v
  have h := independent_original_gauge_intertwining
    theta hCAR hHermitian J hJ g (J.symm v)
  simpa only [J.apply_symm_apply] using h

#print axioms independentOriginalGaugeHom
#print axioms independent_original_gauge_real_covariance
#print axioms independent_original_gauge_intertwining
#print axioms exists_independent_original_gauge_unitary

end
end FCP.IndependentOriginalGaugeBridge
