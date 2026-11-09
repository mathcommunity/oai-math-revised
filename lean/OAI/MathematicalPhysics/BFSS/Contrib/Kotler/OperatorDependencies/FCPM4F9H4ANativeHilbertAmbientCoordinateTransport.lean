import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn

/-!
M4F9 H4A — bridge the ACTUAL independent/source native physical Hilbert
unitaries to the previously accepted exact ambient 17-slot fiber transport.
Only exact coordinate maps; no new charge/operator, no weak hypotheses,
no claims about Hamiltonians, adjoints or spectrum.
-/
set_option autoImplicit false
set_option maxHeartbeats 120000

namespace FCP.M4F9H4ANativeHilbertAmbientCoordinateTransport
noncomputable section
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.IndependentFullL2GaugeTransport
open FCP.IndependentSmoothSupercharge
open FCP.M4F9H2APhysicalHilbertOutputUnitary
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))
variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
  theta α A * theta β B + theta β B * theta α A =
    (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
variable (hHermitian : ∀ α A, (theta α A).IsSymmetric)
variable (J : E ≃ₗᵢ[ℂ] Fermion 2)
variable (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))

/-- Literal physical-input equivalence agrees with fiberTransport after
the actual source physical-subtype inclusion. -/
theorem nativeInput_eq_fiberTransport
    (u : independentPhysicalSpace theta hCAR hHermitian) :
    ((independentPhysicalUnitary theta hCAR hHermitian J hJ u :
      pairedGaugeData.physicalSpace) : FullL2 2) =
    fiberTransport J (u : Lp E 2 μ) := by
  rfl

/-- Literal native Hilbert PiLp 2 output unitary is the same original
fiberTransport on EACH spin index; no use of sup-product Hilbert norms. -/
theorem nativeOutput_apply_eq_fiberTransport
    (v : PiLp 2 (fun _ : SpinIndex =>
        independentPhysicalSpace theta hCAR hHermitian))
    (α : SpinIndex) :
    (((independentPhysicalHilbertOutputUnitary
        theta hCAR hHermitian J hJ v) α :
          pairedGaugeData.physicalSpace) : FullL2 2) =
    fiberTransport J ((v α : independentPhysicalSpace theta hCAR hHermitian) :
      Lp E 2 μ) := by
  rfl

/-- The genuine product of physical-input and native Hilbert-output
unitaries agrees exactly with the accepted DE4 ambient 17-slot transport.
This isolates all coercions before the source-independent graph bridge. -/
theorem nativePair_eq_ambientFiberTransport
    (p : independentPhysicalSpace theta hCAR hHermitian ×
      PiLp 2 (fun _ : SpinIndex =>
        independentPhysicalSpace theta hCAR hHermitian)) :
    (((independentPhysicalUnitary theta hCAR hHermitian J hJ p.1 :
        pairedGaugeData.physicalSpace) : FullL2 2),
      (fun α : SpinIndex =>
        (((independentPhysicalHilbertOutputUnitary
          theta hCAR hHermitian J hJ p.2) α :
            pairedGaugeData.physicalSpace) : FullL2 2))) =
    independentGraphTransportHomeomorph J
      ((p.1 : Lp E 2 μ),
        (fun α : SpinIndex =>
          ((p.2 α : independentPhysicalSpace theta hCAR hHermitian) :
            Lp E 2 μ))) := by
  apply Prod.ext
  · exact nativeInput_eq_fiberTransport theta hCAR hHermitian J hJ p.1
  · funext α
    exact nativeOutput_apply_eq_fiberTransport theta hCAR hHermitian J hJ p.2 α

#print axioms nativeInput_eq_fiberTransport
#print axioms nativeOutput_apply_eq_fiberTransport
#print axioms nativePair_eq_ambientFiberTransport
end
end FCP.M4F9H4ANativeHilbertAmbientCoordinateTransport
