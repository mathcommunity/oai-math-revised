import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentPhysicalUnitary

/-!
M4D1 — independently constructed E-valued smooth compactly supported
test functions, literal independent L2 embedding, and original-source
invariant-core membership bridge.

Uses pinned Mathlib TestFunction.postcompCLM, exact AE-Lp representatives,
and accepted M4C3 membership equivalence. Neither core is defined by
transport, and no unbounded-charge or spectral claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.IndependentSmoothCore
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.IndependentFullL2GaugeTransport
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private abbrev μ := (volume : Measure (Boson 2))

/-- Independent smooth compactly supported E-valued functions on the
original (not renamed) bosonic configuration space. -/
abbrev IndependentTestCore (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] :=
  TestFunction (⊤ : TopologicalSpace.Opens (Boson 2)) E ⊤

/-- L2 inclusion built from the independent function's own compact
support and integrability, before choosing any J. -/
def independentCoreToL2 : IndependentTestCore E →ₗ[ℂ] Lp E 2 μ where
  toFun f := (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).toLp f
  map_add' _ _ := MeasureTheory.MemLp.toLp_add _ _
  map_smul' scalar _ := MeasureTheory.MemLp.toLp_const_smul scalar _

/-- Actual AE representative equation, not pointwise identification
of an arbitrary Lp equivalence class. -/
theorem independentCoreToL2_ae (f : IndependentTestCore E) :
    (independentCoreToL2 f : Boson 2 → E) =ᵐ[μ] f :=
  MemLp.coeFn_toLp (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport)

/-- Fiberwise smooth test-function transport via the pinned Mathlib
postcomposition map. The source target is the literal SmoothCore 2. -/
def independentSmoothTransport (J : E ≃ₗᵢ[ℂ] Fermion 2) :
    IndependentTestCore E →L[ℂ] SmoothCore 2 :=
  TestFunction.postcompCLM J.toContinuousLinearEquiv.toContinuousLinearMap

/-- Direct equality on concrete smooth-function evaluations. -/
theorem independentSmoothTransport_apply (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (f : IndependentTestCore E) (x : Boson 2) :
    independentSmoothTransport J f x = J (f x) := by
  rfl

/-- The pointwise TestFunction fiber map commutes with the true original
L2 quotient embeddings, proved by AE representatives, not by
identifying representatives with arbitrary Lp classes. -/
theorem independentSmoothTransport_coreToL2
    (J : E ≃ₗᵢ[ℂ] Fermion 2) (f : IndependentTestCore E) :
    fiberTransport J (independentCoreToL2 f) =
      coreToL2 (independentSmoothTransport J f) := by
  apply Lp.ext_iff.mpr
  have ha := (J.toContinuousLinearEquiv.toContinuousLinearMap).coeFn_compLpL
    (independentCoreToL2 f)
  have hb := independentCoreToL2_ae f
  have hc := coreToL2_ae (independentSmoothTransport J f)
  filter_upwards [ha, hb, hc] with x ha hb hc
  calc
    (fiberTransport J (independentCoreToL2 f)) x =
        J ((independentCoreToL2 f) x) := ha
    _ = J (f x) := congrArg J hb
    _ = (independentSmoothTransport J f) x :=
      (independentSmoothTransport_apply J f x).symm
    _ = (coreToL2 (independentSmoothTransport J f)) x := hc.symm

variable [FiniteDimensional ℂ E]

variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
  theta α A * theta β B + theta β B * theta α A =
    (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
variable (hHermitian : ∀ α A, (theta α A).IsSymmetric)

/-- Independent invariant test-function submodule, defined by pulling back
the independently defined gauge kernel through the independent core embedding. -/
def independentInvariantCore : Submodule ℂ (IndependentTestCore E) :=
  (independentPhysicalSpace theta hCAR hHermitian).comap independentCoreToL2

/-- Original smooth invariant-core membership iff independent smooth
invariant-core membership for every 48-Majorana generator-preserving J.
The source is literal pairedGaugeData.invariantCore. -/
theorem independentInvariantCore_iff_source
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (f : IndependentTestCore E) :
    f ∈ independentInvariantCore theta hCAR hHermitian ↔
      independentSmoothTransport J f ∈ pairedGaugeData.invariantCore := by
  change independentCoreToL2 f ∈ independentPhysicalSpace theta hCAR hHermitian ↔
    coreToL2 (independentSmoothTransport J f) ∈ pairedGaugeData.physicalSpace
  rw [← independentSmoothTransport_coreToL2 J f]
  exact independentPhysicalSpace_iff_source theta hCAR hHermitian J hJ
    (independentCoreToL2 f)

#print axioms IndependentTestCore
#print axioms independentCoreToL2
#print axioms independentCoreToL2_ae
#print axioms independentSmoothTransport
#print axioms independentSmoothTransport_apply
#print axioms independentSmoothTransport_coreToL2
#print axioms independentInvariantCore
#print axioms independentInvariantCore_iff_source

end
end FCP.IndependentSmoothCore
