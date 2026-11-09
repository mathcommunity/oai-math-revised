import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F8OriginalNamedFullPhysicalGraphDE4
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentPhysicalUnitary
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
BFSS M4F9 H2A — native 16-output PHYSICAL HILBERT unitary.

H1 strictly requalified original-source H=(1/16)T†T on the genuine
PiLp 2 Hilbert direct sum. DE4 accepted an independently defined
physical E2 graph with outputs in a sixteen-coordinate Set/Submodule
of the ordinary (sup-norm) Pi function space.

The product/sup-norm topology may be used for CLOSED GRAPH transport,
but its norm must not be identified with the Hilbert sum norm. Here we
construct the *distinct* genuine PiLp 2 output Hilbert-space unitary
using M4C3B's already accepted genuine independent-to-source physical
fiber unitary on EVERY SpinIndex slot.

This is an output-Hilbert geometry theorem only. It neither changes
the J-free independent E2 charge nor claims any adjoint/H equality.
-/
set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F9H2APhysicalHilbertOutputUnitary
noncomputable section
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
    theta α A * theta β B + theta β B * theta α A =
      (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
variable (hHermitian : ∀ α A, (theta α A).IsSymmetric)
variable (J : E ≃ₗᵢ[ℂ] Fermion 2)
variable (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))

/-- Native physical 16-output Hilbert direct sum transported by
the original source-exact independent SU2 gauge-fiber unitary. -/
noncomputable def independentPhysicalHilbertOutputUnitary :
    PiLp 2 (fun _ : SpinIndex =>
      independentPhysicalSpace theta hCAR hHermitian) ≃ₗᵢ[ℂ]
    PiLp 2 (fun _ : SpinIndex => pairedGaugeData.physicalSpace) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : SpinIndex =>
    independentPhysicalUnitary theta hCAR hHermitian J hJ)

/-- Exactly the accepted original physical unitary on each of the sixteen
slots; no unrelated output renormalization or coordinate permutation. -/
theorem independentPhysicalHilbertOutputUnitary_apply
    (v : PiLp 2 (fun _ : SpinIndex =>
      independentPhysicalSpace theta hCAR hHermitian))
    (α : SpinIndex) :
    independentPhysicalHilbertOutputUnitary theta hCAR hHermitian J hJ v α =
      independentPhysicalUnitary theta hCAR hHermitian J hJ (v α) := by
  rfl

/-- The Hilbert sum norm, not the finite function-space sup norm, is
preserved. This is necessary for a legitimate Hilbert adjoint transfer. -/
theorem independentPhysicalHilbertOutputUnitary_norm
    (v : PiLp 2 (fun _ : SpinIndex =>
      independentPhysicalSpace theta hCAR hHermitian)) :
    ‖independentPhysicalHilbertOutputUnitary theta hCAR hHermitian J hJ v‖ =
      ‖v‖ := by
  exact (independentPhysicalHilbertOutputUnitary theta hCAR hHermitian J hJ).norm_map v

#print axioms independentPhysicalHilbertOutputUnitary
#print axioms independentPhysicalHilbertOutputUnitary_apply
#print axioms independentPhysicalHilbertOutputUnitary_norm

end
end FCP.M4F9H2APhysicalHilbertOutputUnitary
