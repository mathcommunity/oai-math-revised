import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AFOriginalSmoothParityInvolutionProbe
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# H5E8AI — exact original FullL2 parity from Euclidean Lebesgue invariance

Build genuine complex-linear isometry of the *original* FullL2 N,
induced by the original Boson N spatial inversion x ↦ -x.
The only analytic input is pinned Mathlib's proof that a real linear
isometry equivalence preserves finite-dimensional Euclidean volume.
Establish compatibility with the *actual source* coreToL2 embedding.

Kernel-qualification required: this is a research candidate. Its
existence does NOT yet imply source SU2 gauge invariance, a physical
restricted graph, the associated Hamiltonian operator domain, or
equivalence of the manuscript's independently specified Cl(48) model.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AI
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AF
open MeasureTheory

/-- The original bosonic inversion is real-linearly isometric.
There is no new Euclidean-space or matrix convention. -/
noncomputable def originalBosonNeg {N : ℕ} :
    Boson N ≃ₗᵢ[ℝ] Boson N :=
  LinearIsometryEquiv.neg ℝ

theorem originalBosonNeg_apply {N : ℕ} (x : Boson N) :
    originalBosonNeg x = -x := rfl

/-- Lebesgue measure on the original bosonic Euclidean space is
invariant under the *exact* full-coordinate inversion. -/
theorem originalBosonNeg_measurePreserving {N : ℕ} :
    MeasurePreserving (fun x : Boson N => -x)
      (volume : Measure (Boson N)) (volume : Measure (Boson N)) := by
  change MeasurePreserving (originalBosonNeg (N := N))
  exact (originalBosonNeg (N := N)).measurePreserving

/-- Actual FullL2 parity is a complex-linear isometry, not an
unbounded pointwise operation on arbitrary L2 representatives. -/
noncomputable def originalFullL2Parity {N : ℕ} :
    FullL2 N →ₗᵢ[ℂ] FullL2 N :=
  Lp.compMeasurePreservingₗᵢ ℂ
    (fun x : Boson N => -x) originalBosonNeg_measurePreserving

/-- Correct almost-everywhere representative semantics for original L2. -/
theorem originalFullL2Parity_apply_ae {N : ℕ} (g : FullL2 N) :
    (originalFullL2Parity g : Boson N → Fermion N)
      =ᵐ[volume] (fun x : Boson N => g (-x)) := by
  exact Lp.coeFn_compMeasurePreserving g originalBosonNeg_measurePreserving

/-- The L2 parity is compatible with the *literal original*
SmoothCore-to-FullL2 embedding of pinned upstream BFSS Core. -/
theorem originalFullL2Parity_coreToL2 {N : ℕ} (f : SmoothCore N) :
    originalFullL2Parity (coreToL2 f) =
      coreToL2 (originalSmoothParity f) := by
  let hf : MemLp (f : Boson N → Fermion N) 2 volume :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have h := Lp.toLp_compMeasurePreserving hf
    (originalBosonNeg_measurePreserving (N := N))
  exact h

#print axioms originalBosonNeg
#print axioms originalBosonNeg_measurePreserving
#print axioms originalFullL2Parity
#print axioms originalFullL2Parity_apply_ae
#print axioms originalFullL2Parity_coreToL2

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AI
