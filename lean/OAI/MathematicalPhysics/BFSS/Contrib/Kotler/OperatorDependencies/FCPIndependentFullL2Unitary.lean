import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentFullL2GaugeTransport

/-!
M4C2 — strict source-exact full-L² constant-fiber unitary candidate.

M4C1 already proves exact original SU(2) full-space gauge intertwining
under the M4B source-exact generator hypotheses. This separate gate proves
that its constant-fiber continuous-linear operator is bijective and isometric.
There is no new gauge choice, source reinterpretation, smooth-core claim,
physical fixed-space identification, unbounded-operator or spectral claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.IndependentFullL2GaugeTransport
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private abbrev μ := (volume : Measure (Boson 2))

/-- The fiberwise map followed by the literally inverse constant-fiber map
is the identity on the original-independent L² quotient, not merely on
representative functions. -/
theorem fiberTransport_left_inverse
    (J : E ≃ₗᵢ[ℂ] Fermion 2) (v : Lp E 2 μ) :
    (J.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ)
      (fiberTransport J v) = v := by
  apply Lp.ext_iff.mpr
  have hforward := (J.toContinuousLinearEquiv.toContinuousLinearMap).coeFn_compLpL v
  have hback := (J.symm.toContinuousLinearEquiv.toContinuousLinearMap).coeFn_compLpL
    (fiberTransport J v)
  filter_upwards [hforward, hback] with x hf hb
  calc
    ((J.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ)
      (fiberTransport J v)) x = J.symm ((fiberTransport J v) x) := hb
    _ = J.symm (J (v x)) := by
      exact congrArg J.symm hf
    _ = v x := J.symm_apply_apply _

/-- The source-to-independent fiberwise inverse is also a right inverse
on the actual source `FullL2 2` quotient. -/
theorem fiberTransport_right_inverse
    (J : E ≃ₗᵢ[ℂ] Fermion 2) (v : FullL2 2) :
    fiberTransport J
      ((J.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ) v) = v := by
  apply Lp.ext_iff.mpr
  have hback := (J.symm.toContinuousLinearEquiv.toContinuousLinearMap).coeFn_compLpL v
  have hforward := (J.toContinuousLinearEquiv.toContinuousLinearMap).coeFn_compLpL
    ((J.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ) v)
  filter_upwards [hback, hforward] with x hb hf
  calc
    (fiberTransport J
      ((J.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ) v)) x =
        J (((J.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ) v) x) := hf
    _ = J (J.symm (v x)) := by
      exact congrArg J hb
    _ = v x := J.apply_symm_apply _

/-- Explicit full L² linear equivalence with the genuine inverse induced by
J.symm; isometry is verified separately, not inferred from linearity. -/
def fiberTransportLinearEquiv
    (J : E ≃ₗᵢ[ℂ] Fermion 2) : Lp E 2 μ ≃ₗ[ℂ] FullL2 2 where
  toFun := fiberTransport J
  invFun := J.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ
  left_inv := fiberTransport_left_inverse J
  right_inv := fiberTransport_right_inverse J
  map_add' := (fiberTransport J).map_add
  map_smul' := (fiberTransport J).map_smul

/-- The M4C1 full-space fiber map is contractive, by norm-one-fiber
isometry and the exact pinned Mathlib Lp operator bound. -/
theorem fiberTransport_norm_le
    (J : E ≃ₗᵢ[ℂ] Fermion 2) (v : Lp E 2 μ) :
    ‖fiberTransport J v‖ ≤ ‖v‖ := by
  let A : E →L[ℂ] Fermion 2 :=
    J.toContinuousLinearEquiv.toContinuousLinearMap
  have hA : ‖A‖ ≤ 1 := by
    change ‖J.toLinearIsometry.toContinuousLinearMap‖ ≤ 1
    exact J.toLinearIsometry.norm_toContinuousLinearMap_le
  calc
    ‖fiberTransport J v‖ ≤ ‖A‖ * ‖v‖ := by
      change ‖A.compLp v‖ ≤ ‖A‖ * ‖v‖
      exact A.norm_compLp_le v
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _ = ‖v‖ := one_mul _

/-- The exact Lp inverse fiber map is likewise contractive. -/
theorem inverseFiberTransport_norm_le
    (J : E ≃ₗᵢ[ℂ] Fermion 2) (v : FullL2 2) :
    ‖(J.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ) v‖ ≤ ‖v‖ := by
  let A : Fermion 2 →L[ℂ] E :=
    J.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hA : ‖A‖ ≤ 1 := by
    change ‖J.symm.toLinearIsometry.toContinuousLinearMap‖ ≤ 1
    exact J.symm.toLinearIsometry.norm_toContinuousLinearMap_le
  calc
    ‖(J.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ) v‖ ≤
        ‖A‖ * ‖v‖ := by
      change ‖A.compLp v‖ ≤ ‖A‖ * ‖v‖
      exact A.norm_compLp_le v
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _ = ‖v‖ := one_mul _

/-- Genuine complex-linear unitary equivalence of the independent full
L² fiber realization and the ORIGINAL BFSS source FullL2 2, whose
forward map is definitionally M4C1's fiberTransport. -/
def fiberTransportUnitary
    (J : E ≃ₗᵢ[ℂ] Fermion 2) : Lp E 2 μ ≃ₗᵢ[ℂ] FullL2 2 :=
  LinearIsometryEquiv.ofBounds (fiberTransportLinearEquiv J)
    (fiberTransport_norm_le J)
    (by
      intro v
      exact inverseFiberTransport_norm_le J v)

#print axioms fiberTransport_left_inverse
#print axioms fiberTransport_right_inverse
#print axioms fiberTransportLinearEquiv
#print axioms fiberTransport_norm_le
#print axioms inverseFiberTransport_norm_le
#print axioms fiberTransportUnitary

end
end FCP.IndependentFullL2GaugeTransport
