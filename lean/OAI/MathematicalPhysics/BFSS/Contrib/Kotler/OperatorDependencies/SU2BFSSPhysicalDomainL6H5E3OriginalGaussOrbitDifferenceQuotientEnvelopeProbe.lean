import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E2OriginalGaussOrbitDifferenceEnvelopeProbe

/-!
L6H5E3 — the ORIGINAL source SU2 difference quotients have
a single, square-integrable majorant independent of real t ≠ 0.

The generic normed-space scalar estimate is separated from the
exact source FullL2 representation: only the already-qualified
H5E2 finite-difference envelope is used. The quotient is the
REAL scalar inverse t⁻¹ acting on the unchanged source Fock fiber.

This does not assert dominated convergence, FullL2 norm
differentiability, self-adjointness or any BFSS spectral result.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E3
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6H0
open FCP.BFSSSU2PhysicalDomainL6H5E2
open MeasureTheory

/-- Generic vector-valued inverse-time scalar division does not
enlarge a linear-in-|t| finite difference bound. -/
theorem norm_inv_smul_le_of_linear_time_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (C t : ℝ) (ht : t ≠ 0)
    (hv : ‖v‖ ≤ C * |t|) :
    ‖(t⁻¹) • v‖ ≤ C := by
  have hat : |t| ≠ 0 := abs_ne_zero.mpr ht
  calc
    ‖(t⁻¹) • v‖ = |t|⁻¹ * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv]
    _ ≤ |t|⁻¹ * (C * |t|) :=
      mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr (abs_nonneg t))
    _ = C := by
      calc
        |t|⁻¹ * (C * |t|) = C * (|t| * |t|⁻¹) := by ring
        _ = C := by rw [mul_inv_cancel₀ hat, mul_one]

/-- A single squared-integrable source radial envelope bounds EVERY
nonzero-time REAL difference quotient of the original gauge orbit
on the actual Fock fiber. This is pointwise in the original boson
configuration and precedes the real FullL2 dominated-convergence
bridge. -/
theorem actualOriginalGaussOrbit_differenceQuotient_integrableEnvelope
    (c : ColorIndex 2) (f : SmoothCore 2) :
    ∃ (R C : ℝ), 0 < R ∧ 0 ≤ C ∧
      Integrable (fun x : Boson 2 =>
        (if ‖x‖ < R then C else 0) ^ 2)
        (volume : Measure (Boson 2)) ∧
      ∀ (t : ℝ), t ≠ 0 → ∀ (x : Boson 2),
        ‖(t⁻¹) •
          (actualOriginalSmoothGaugeOrbitRepresentative f
              (sourcePlusIGaugeCurve c t) x -
            actualOriginalSmoothGaugeOrbitRepresentative f
              (sourcePlusIGaugeCurve c 0) x)‖ ≤
          (if ‖x‖ < R then C else 0) := by
  obtain ⟨R, C, hR, hC, hint, hbound⟩ :=
    actualOriginalGaussOrbit_difference_integrableEnvelope c f
  refine ⟨R, C, hR, hC, hint, ?_⟩
  intro t ht x
  exact norm_inv_smul_le_of_linear_time_bound
    (actualOriginalSmoothGaugeOrbitRepresentative f
      (sourcePlusIGaugeCurve c t) x -
    actualOriginalSmoothGaugeOrbitRepresentative f
      (sourcePlusIGaugeCurve c 0) x)
    (if ‖x‖ < R then C else 0) t ht (hbound t x)

#print axioms norm_inv_smul_le_of_linear_time_bound
#print axioms actualOriginalGaussOrbit_differenceQuotient_integrableEnvelope
#check @norm_inv_smul_le_of_linear_time_bound
#check @actualOriginalGaussOrbit_differenceQuotient_integrableEnvelope

end
end FCP.BFSSSU2PhysicalDomainL6H5E3
