import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentOriginalGaugeBridge
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4JExactGaugeDataAssemblyProbe
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
M4C1 — prospective source-specific theorem; source `.olean` closure unavailable
locally. Transport the actual original full-L² gauge action along the M4B
fiberwise unitary; no arbitrary new gauge representation or source core.
Invariance, smooth-core preservation, closed operators and spectrum require
separate theorems.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.IndependentFullL2GaugeTransport
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4B
open FCP.BFSSSU2GaugeG4J
open FCP.IndependentOriginalGaugeBridge
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

private abbrev μ := (volume : Measure (Boson 2))
private abbrev IndependentFullL2 (E : Type*) [NormedAddCommGroup E] := Lp E 2 μ

variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
  theta α A * theta β B + theta β B * theta α A =
    (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
variable (hHermitian : ∀ α A, (theta α A).IsSymmetric)

/-- The exact ORIGINAL bosonic inverse pullback with the independently
constructed, J-free M4B fermionic Spin gauge action. -/
def independentFullL2GaugePairCLM (g : GaugeGroup 2) :
    IndependentFullL2 E →L[ℂ] IndependentFullL2 E :=
  ((independentOriginalGaugeHom theta hCAR hHermitian g).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    2 μ).comp
  ((Lp.compMeasurePreservingₗᵢ ℂ (pairedGaugeData.boson g⁻¹)
    (pairedGaugeData.boson g⁻¹).measurePreserving).toContinuousLinearMap)

/-- Constant-fiber map from arbitrary eligible independent Majorana
Hilbert module to the actual original BFSS source FullL2 2. -/
def fiberTransport (J : E ≃ₗᵢ[ℂ] Fermion 2) :
    IndependentFullL2 E →L[ℂ] FullL2 2 :=
  J.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ

omit [FiniteDimensional ℂ E] in
/-- Crucial Lp naturality: constant fiber maps commute with the
source's literal measure-preserving bosonic pullback. -/
theorem fiberTransport_bosonPullback
    (J : E ≃ₗᵢ[ℂ] Fermion 2) (g : GaugeGroup 2)
    (v : IndependentFullL2 E) :
    fiberTransport J
      ((Lp.compMeasurePreservingₗᵢ ℂ (pairedGaugeData.boson g)
        (pairedGaugeData.boson g).measurePreserving).toContinuousLinearMap v) =
      pairedGaugeData.bosonPullback g (fiberTransport J v) := by
  let A : E →L[ℂ] Fermion 2 := J.toContinuousLinearEquiv.toContinuousLinearMap
  let b := pairedGaugeData.boson g
  let hb : MeasurePreserving b μ μ := (pairedGaugeData.boson g).measurePreserving
  change A.compLp (Lp.compMeasurePreserving b hb v) =
    Lp.compMeasurePreserving b hb (A.compLp v)
  apply Lp.ext_iff.mpr
  have hleft := A.coeFn_compLp (Lp.compMeasurePreserving b hb v)
  have hpull := Lp.coeFn_compMeasurePreserving v hb
  have hright := Lp.coeFn_compMeasurePreserving (A.compLp v) hb
  have hmid := (A.coeFn_compLp' v).comp_tendsto
    hb.quasiMeasurePreserving.tendsto_ae
  filter_upwards [hleft, hpull, hright, hmid] with x hl hp hr hm
  calc
    (A.compLp (Lp.compMeasurePreserving b hb v)) x =
        A ((Lp.compMeasurePreserving b hb v) x) := hl
    _ = A (v (b x)) := by
      simpa only [Function.comp_apply] using congrArg A hp
    _ = (A.compLp v) (b x) := hm.symm
    _ = (Lp.compMeasurePreserving b hb (A.compLp v)) x := hr.symm

/-- Exact M4B fermionic group intertwining lifted to the original
spatial L² space, with no choice of L² representatives. -/
theorem fiberTransport_fermionGauge
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (g : GaugeGroup 2) (v : IndependentFullL2 E) :
    fiberTransport J
      (((independentOriginalGaugeHom theta hCAR hHermitian g).toContinuousLinearEquiv.toContinuousLinearMap).compLpL 2 μ v) =
      pairedGaugeData.fiberAction g (fiberTransport J v) := by
  let A : E →L[ℂ] Fermion 2 := J.toContinuousLinearEquiv.toContinuousLinearMap
  let B : E →L[ℂ] E :=
    (independentOriginalGaugeHom theta hCAR hHermitian g).toContinuousLinearEquiv.toContinuousLinearMap
  let C : Fermion 2 →L[ℂ] Fermion 2 :=
    (pairedGaugeData.fermion g).toContinuousLinearEquiv.toContinuousLinearMap
  have hpoint (w : E) : A (B w) = C (A w) := by
    change J (independentOriginalGaugeHom theta hCAR hHermitian g w) =
      pairedGaugeData.fermion g (J w)
    calc
      _ = fermionGaugeLinearEquiv g (J w) :=
        independent_original_gauge_intertwining theta hCAR hHermitian J hJ g w
      _ = pairedGaugeData.fermion g (J w) := by
        rw [pairedGaugeData_fermion_exact]
        rfl
  change A.compLp (B.compLp v) = C.compLp (A.compLp v)
  apply Lp.ext_iff.mpr
  have ha := A.coeFn_compLp (B.compLp v)
  have hb := B.coeFn_compLp v
  have hc := C.coeFn_compLp (A.compLp v)
  have hd := A.coeFn_compLp v
  filter_upwards [ha, hb, hc, hd] with x ha hb hc hd
  calc
    (A.compLp (B.compLp v)) x = A ((B.compLp v) x) := ha
    _ = A (B (v x)) := by rw [hb]
    _ = C (A (v x)) := hpoint (v x)
    _ = C ((A.compLp v) x) := by rw [hd]
    _ = (C.compLp (A.compLp v)) x := hc.symm

/-- M4C1 source-exact full-L² SU2 gauge intertwiner: preserves original
inverse-bosonic-pullback convention, not just finite Fock fibers. -/
theorem independentFullL2Gauge_intertwining
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (g : GaugeGroup 2) (v : IndependentFullL2 E) :
    fiberTransport J (independentFullL2GaugePairCLM theta hCAR hHermitian g v) =
      pairedGaugeData.fiberAction g
        (pairedGaugeData.bosonPullback g⁻¹ (fiberTransport J v)) := by
  change fiberTransport J
    (((independentOriginalGaugeHom theta hCAR hHermitian g).toContinuousLinearEquiv.toContinuousLinearMap).compLpL
      2 μ
      ((Lp.compMeasurePreservingₗᵢ ℂ (pairedGaugeData.boson g⁻¹)
        (pairedGaugeData.boson g⁻¹).measurePreserving).toContinuousLinearMap v)) = _
  rw [fiberTransport_fermionGauge theta hCAR hHermitian J hJ g]
  rw [fiberTransport_bosonPullback J g⁻¹ v]

#print axioms independentFullL2GaugePairCLM
#print axioms fiberTransport
#print axioms fiberTransport_bosonPullback
#print axioms fiberTransport_fermionGauge
#print axioms independentFullL2Gauge_intertwining

end
end FCP.IndependentFullL2GaugeTransport
