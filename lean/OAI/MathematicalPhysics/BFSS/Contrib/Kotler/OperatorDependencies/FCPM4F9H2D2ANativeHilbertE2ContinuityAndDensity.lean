import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H2D1ActualE2HilbertOutputDomainEquivalence
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F8IndependentActualE2FullPhysicalDomainDE2B

/-!
BFSS M4F9 H2D2A — true independent E2 native Hilbert output
coordinate continuity and unconditional physical input domain density.

Do not identify the finite product/sup norm with PiLp 2 Hilbert norm.
Continuity follows from native PiLp coordinate continuity, literal
physical subtype inclusions and the product topology. Density follows
from actual independently defined DE2B E2 domain density and H2D1's
exact natural domain iff. The original E2 graph/operator is not changed.
No source charge/Hamiltonian or spectral claim is introduced.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H2D2ANativeHilbertE2ContinuityAndDensity
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.M4F9H2BPhysicalHilbertE2GraphRebase
open FCP.M4F9H2CActualE2NativeHilbertChargeColumn
open FCP.M4F9H2D1ActualE2HilbertOutputDomainEquivalence
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))
variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
  theta α A * theta β B + theta β B * theta α A =
    (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
variable (hHermitian : ∀ α A, (theta α A).IsSymmetric)

/-- Norm-topological continuity of the ACTUAL output-coordinate map
from genuine Hilbert PiLp 2 (no identification with sup-product norm). -/
theorem hilbertPhysicalOutputsToActualOutputs_continuous :
    Continuous (hilbertPhysicalOutputsToActualOutputs
      theta hCAR hHermitian) := by
  have hraw :
      Continuous (fun v : PiLp 2 (fun _ : SpinIndex =>
        independentPhysicalSpace theta hCAR hHermitian) =>
        (fun α : SpinIndex => (v α : Lp E 2 μ))) := by
    apply continuous_pi
    intro α
    exact continuous_subtype_val.comp
      (PiLp.continuous_apply 2
        (fun _ : SpinIndex => independentPhysicalSpace theta hCAR hHermitian) α)
  exact hraw.subtype_mk (fun v =>
    (hilbertPhysicalOutputsToActualOutputs theta hCAR hHermitian v).property)

variable (color : ColorIndex 2 → ColorMatrix 2)
variable (gamma : SpaceIndex → GammaMatrix)

/-- Unconditional dense natural DOMAIN of native independent physical
PiLp 2 E2 Hilbert charge: exactly the original DE2B dense domain,
with original source/representation witness conditions used ONLY in
the analytic parent theorem and never to define this J-free charge. -/
theorem independentActualE2NativeHilbertChargeColumn_domain_dense
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w)) :
    Dense ((independentActualE2NativeHilbertChargeColumn
      theta hCAR hHermitian color gamma).domain :
        Set (independentPhysicalSpace theta hCAR hHermitian)) := by
  have hset :
      ((independentActualE2NativeHilbertChargeColumn
        theta hCAR hHermitian color gamma).domain :
          Set (independentPhysicalSpace theta hCAR hHermitian)) =
      ((FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn
        color gamma theta hCAR hHermitian).domain :
          Set (independentPhysicalSpace theta hCAR hHermitian)) := by
    ext u
    exact independentActualE2NativeHilbertChargeColumn_domain_iff
      theta hCAR hHermitian color gamma u
  rw [hset]
  exact FCP.M4F8IndependentActualE2FullPhysicalDomainDE2B.independentActualE2FullPhysicalChargeColumn_domain_dense
    color gamma theta hCAR hHermitian J hColor hGamma hJ

#print axioms hilbertPhysicalOutputsToActualOutputs_continuous
#print axioms independentActualE2NativeHilbertChargeColumn_domain_dense

end
end FCP.M4F9H2D2ANativeHilbertE2ContinuityAndDensity
