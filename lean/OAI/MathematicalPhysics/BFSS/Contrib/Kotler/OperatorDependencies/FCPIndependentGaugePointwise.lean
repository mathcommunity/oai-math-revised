import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentInvariantSmoothEquiv

/-!
M4D3 — exact pointwise gauge-fixed smooth-core identification.

The literal original pairedGaugeData.invariantCore is equivalent to
pointwise covariance f (boson g x) = fermion g (f x), including the
previously absent converse via actual AE-L2 representatives.

For the independent E-valued source, the corresponding pointwise
action is the M4B native-Spin fermion gauge homomorphism, defined
without selecting J. Its iff is derived from the already qualified
M4D1 smooth-core membership and the original gauge intertwiner.

The resulting pointwise equation is the fixed-vector equation of
the manuscript combined action V_g f (O_g^-1 x), with the same
original bosonic inverse convention. This candidate makes no
supercharge, domain, Hamiltonian, or spectrum claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.IndependentGaugePointwise
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4B FCP.BFSSSU2GaugeG4J
open FCP.IndependentOriginalGaugeBridge
open FCP.IndependentPhysicalSpace
open FCP.IndependentSmoothCore
open MeasureTheory

/-- Both directions of the literal original invariant-core pointwise
gauge condition. The reverse direction uses original coreToL2_ae
and measure-preserving bosonic pullback, not an assumed equality of
pointwise and L2 classes. -/
theorem originalInvariantCore_pointwise_iff (f : SmoothCore 2) :
    f ∈ pairedGaugeData.invariantCore ↔
      ∀ (g : GaugeGroup 2) (x : Boson 2),
        f (pairedGaugeData.boson g x) =
          pairedGaugeData.fermion g (f x) := by
  constructor
  · intro hf g x
    exact pairedGaugeData.invariantCore_equivariant ⟨f, hf⟩ g x
  · intro hf
    change coreToL2 f ∈ pairedGaugeData.physicalSpace
    apply (originalPhysicalSpace_mem_iff (coreToL2 f)).2
    intro g
    apply Lp.ext_iff.mpr
    have hb := Lp.coeFn_compMeasurePreserving (coreToL2 f)
      (pairedGaugeData.boson g).measurePreserving
    have hferm := ContinuousLinearMap.coeFn_compLp
      (pairedGaugeData.fermion g).toContinuousLinearEquiv.toContinuousLinearMap
      (coreToL2 f)
    have hcore := coreToL2_ae f
    have hcorecomp := hcore.comp_tendsto
      (pairedGaugeData.boson g).measurePreserving.quasiMeasurePreserving.tendsto_ae
    filter_upwards [hb, hferm, hcore, hcorecomp] with x hb hferm hcore hcorecomp
    calc
      (pairedGaugeData.bosonPullback g (coreToL2 f)) x =
          (coreToL2 f) (pairedGaugeData.boson g x) := hb
      _ = f (pairedGaugeData.boson g x) := hcorecomp
      _ = pairedGaugeData.fermion g (f x) := hf g x
      _ = pairedGaugeData.fermion g ((coreToL2 f) x) :=
        congrArg (pairedGaugeData.fermion g) hcore.symm
      _ = (pairedGaugeData.fiberAction g (coreToL2 f)) x := hferm.symm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
  theta α A * theta β B + theta β B * theta α A =
    (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
variable (hHermitian : ∀ α A, (theta α A).IsSymmetric)

/-- Independently formulated native-Spin pointwise gauge covariance
is equivalent to membership in the independent invariant smooth core.
No independent gauge action or core is defined by transporting J.

The source-exact J occurs only in the proof of the iff; qualified
M3J already gives its existence under the intended irreducibility
hypothesis. -/
theorem independentInvariantCore_pointwise_iff
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (f : IndependentTestCore E) :
    f ∈ independentInvariantCore theta hCAR hHermitian ↔
      ∀ (g : GaugeGroup 2) (x : Boson 2),
        f (pairedGaugeData.boson g x) =
          independentOriginalGaugeHom theta hCAR hHermitian g (f x) := by
  constructor
  · intro hf g x
    have hs :
        (independentSmoothTransport J f)
            (pairedGaugeData.boson g x) =
          pairedGaugeData.fermion g ((independentSmoothTransport J f) x) :=
      (originalInvariantCore_pointwise_iff (independentSmoothTransport J f)).1
        ((independentInvariantCore_iff_source theta hCAR hHermitian J hJ f).1 hf) g x
    apply J.injective
    calc
      J (f (pairedGaugeData.boson g x)) =
          (independentSmoothTransport J f) (pairedGaugeData.boson g x) :=
            (independentSmoothTransport_apply J f _).symm
      _ = pairedGaugeData.fermion g ((independentSmoothTransport J f) x) := hs
      _ = pairedGaugeData.fermion g (J (f x)) := by
        rw [independentSmoothTransport_apply]
      _ = J (independentOriginalGaugeHom theta hCAR hHermitian g (f x)) := by
        rw [pairedGaugeData_fermion_exact]
        exact (independent_original_gauge_intertwining
          theta hCAR hHermitian J hJ g (f x)).symm
  · intro hf
    apply (independentInvariantCore_iff_source theta hCAR hHermitian J hJ f).2
    apply (originalInvariantCore_pointwise_iff (independentSmoothTransport J f)).2
    intro g x
    calc
      (independentSmoothTransport J f) (pairedGaugeData.boson g x) =
          J (f (pairedGaugeData.boson g x)) :=
            independentSmoothTransport_apply J f _
      _ = J (independentOriginalGaugeHom theta hCAR hHermitian g (f x)) :=
        congrArg J (hf g x)
      _ = fermionGaugeLinearEquiv g (J (f x)) :=
        independent_original_gauge_intertwining
          theta hCAR hHermitian J hJ g (f x)
      _ = pairedGaugeData.fermion g (J (f x)) := by
        rw [pairedGaugeData_fermion_exact]
        rfl
      _ = pairedGaugeData.fermion g ((independentSmoothTransport J f) x) := by
        rw [independentSmoothTransport_apply]

#print axioms originalInvariantCore_pointwise_iff
#print axioms independentInvariantCore_pointwise_iff

end
end FCP.IndependentGaugePointwise
