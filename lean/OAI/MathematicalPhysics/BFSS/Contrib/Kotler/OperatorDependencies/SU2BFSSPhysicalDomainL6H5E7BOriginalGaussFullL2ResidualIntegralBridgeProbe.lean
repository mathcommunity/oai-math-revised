import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E7AOriginalFullL2NormSquareIntegralBridgeProbe

/-!
L6H5E7B — identify the true ORIGINAL BFSS FullL2 Gauss
difference-quotient residual with H5E6C's pointwise squared-error
integral, using H0's source-exact almost-everywhere representative.

The only new generic calculation is how a real-scaled difference
of complex L2 functions and a third L2 vector are represented a.e.
The genuine inverse-boson SU2 orbit, original 48-Majorana Fock
fiber, plus-i color curve and Gauss candidate remain unchanged.

NOT YET a strong derivative or a generator-domain theorem.
No extra axioms, surrogate gauge action, or spectral claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E7B
noncomputable section

open scoped Topology
open MeasureTheory
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6H0
open FCP.BFSSSU2PhysicalDomainL6H5B
open FCP.BFSSSU2PhysicalDomainL6H5E6B
open FCP.BFSSSU2PhysicalDomainL6H5E7A

/-- Abstract L2 representative of the real-scaled affine residual.
The source Fock type is deliberately absent from this lemma. -/
theorem abstractComplexL2_realAffineResidual_ae
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (μ : Measure α) (u v w : Lp E 2 μ) (s : ℝ) :
    ((s • (u - v) - w : Lp E 2 μ) : α → E) =ᵐ[μ]
      (fun x => s • (u x - v x) - w x) := by
  filter_upwards
    [Lp.coeFn_sub (s • (u - v)) w,
      Lp.coeFn_smul s (u - v),
      Lp.coeFn_sub u v] with x hsub hsmul hdiff
  -- #309: coeFn_sub and coeFn_smul first produce function-level
  -- differences/smuls, not their evaluated pointwise versions.
  have hsub' :
      (s • (u - v) - w : Lp E 2 μ) x =
        (s • (u - v) : Lp E 2 μ) x - w x := by
    simpa only [Pi.sub_apply] using hsub
  have hsmul' :
      (s • (u - v) : Lp E 2 μ) x = s • (u - v : Lp E 2 μ) x := by
    simpa only [Pi.smul_apply] using hsmul
  have hdiff' :
      (u - v : Lp E 2 μ) x = u x - v x := by
    simpa only [Pi.sub_apply] using hdiff
  calc
    (s • (u - v) - w : Lp E 2 μ) x =
        (s • (u - v) : Lp E 2 μ) x - w x := hsub'
    _ = s • ((u - v : Lp E 2 μ) x) - w x := by rw [hsmul']
    _ = s • (u x - v x) - w x := by rw [hdiff']

/-- The exact strong-Hilbert residual of the genuine source +i SU2
gauge orbit, before its convergence has been proved. -/
noncomputable def actualOriginalGaussFullL2Residual
    (c : ColorIndex 2) (f : SmoothCore 2) (t : ℝ) : FullL2 2 :=
  (t⁻¹ : ℝ) •
    (actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c t) (coreToL2 f) -
     actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c 0) (coreToL2 f)) -
    coreToL2 (actualOriginalCoreColorGaussCandidate c f)

/-- The exact FullL2 residual is represented almost everywhere
by the original pointwise Fock squared-error integrand's vector. -/
theorem actualOriginalGaussFullL2Residual_ae
    (c : ColorIndex 2) (f : SmoothCore 2) (t : ℝ) :
    (actualOriginalGaussFullL2Residual c f t :
      Boson 2 → Fermion 2) =ᵐ[volume]
      (fun x : Boson 2 =>
        (t⁻¹ : ℝ) •
          (actualOriginalSmoothGaugeOrbitRepresentative f
              (sourcePlusIGaugeCurve c t) x -
           actualOriginalSmoothGaugeOrbitRepresentative f
              (sourcePlusIGaugeCurve c 0) x) -
          (actualOriginalCoreColorGaussCandidate c f) x) := by
  let u : FullL2 2 :=
    actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c t) (coreToL2 f)
  let v : FullL2 2 :=
    actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c 0) (coreToL2 f)
  let w : FullL2 2 :=
    coreToL2 (actualOriginalCoreColorGaussCandidate c f)
  have habstract :
      ((t⁻¹ : ℝ) • (u - v) - w : FullL2 2) =ᵐ[volume]
        (fun x : Boson 2 => (t⁻¹ : ℝ) • (u x - v x) - w x) :=
    abstractComplexL2_realAffineResidual_ae
      (μ := (volume : Measure (Boson 2))) u v w (t⁻¹)
  -- #309: pin the H0 source a.e. identities to the *named*
  -- FullL2 arguments u/v/w before performing the pointwise rewrite.
  -- Rewriting against an opaque let binding otherwise fails to match.
  have hu :
      (u : Boson 2 → Fermion 2) =ᵐ[volume]
        (fun x : Boson 2 =>
          actualOriginalSmoothGaugeOrbitRepresentative f
            (sourcePlusIGaugeCurve c t) x) :=
    actualOriginalSmoothGaugeOrbit_ae_fullL2 f (sourcePlusIGaugeCurve c t)
  have hv :
      (v : Boson 2 → Fermion 2) =ᵐ[volume]
        (fun x : Boson 2 =>
          actualOriginalSmoothGaugeOrbitRepresentative f
            (sourcePlusIGaugeCurve c 0) x) :=
    actualOriginalSmoothGaugeOrbit_ae_fullL2 f (sourcePlusIGaugeCurve c 0)
  have hw :
      (w : Boson 2 → Fermion 2) =ᵐ[volume]
        (fun x : Boson 2 =>
          (actualOriginalCoreColorGaussCandidate c f) x) :=
    coreToL2_ae (actualOriginalCoreColorGaussCandidate c f)
  filter_upwards [habstract, hu, hv, hw]
    with x hab hx hz hg
  calc
    (actualOriginalGaussFullL2Residual c f t :
      Boson 2 → Fermion 2) x =
        (t⁻¹ : ℝ) • (u x - v x) - w x := hab
    _ = (t⁻¹ : ℝ) •
          (actualOriginalSmoothGaugeOrbitRepresentative f
            (sourcePlusIGaugeCurve c t) x -
           actualOriginalSmoothGaugeOrbitRepresentative f
            (sourcePlusIGaugeCurve c 0) x) -
          (actualOriginalCoreColorGaussCandidate c f) x := by
          rw [hx, hz, hg]

/-- No hidden representative identification: the exact squared
FullL2 norm of the genuine source Gauss quotient residual equals
the already-qualified pointwise squared-error integral. -/
theorem actualOriginalGaussFullL2Residual_norm_sq_eq_integral
    (c : ColorIndex 2) (f : SmoothCore 2) (t : ℝ) :
    ‖actualOriginalGaussFullL2Residual c f t‖ ^ 2 =
      ∫ x : Boson 2,
        actualOriginalGaussQuotientSquaredError c f t x
          ∂(volume : Measure (Boson 2)) := by
  calc
    ‖actualOriginalGaussFullL2Residual c f t‖ ^ 2 =
        ∫ x : Boson 2,
          ‖(actualOriginalGaussFullL2Residual c f t :
            Boson 2 → Fermion 2) x‖ ^ 2
          ∂(volume : Measure (Boson 2)) :=
      actualOriginalFullL2_norm_sq_eq_integral
        (actualOriginalGaussFullL2Residual c f t)
    _ = ∫ x : Boson 2,
          actualOriginalGaussQuotientSquaredError c f t x
          ∂(volume : Measure (Boson 2)) := by
      apply integral_congr_ae
      filter_upwards [actualOriginalGaussFullL2Residual_ae c f t] with x hx
      rw [hx]
      rfl

#print axioms abstractComplexL2_realAffineResidual_ae
#print axioms actualOriginalGaussFullL2Residual
#print axioms actualOriginalGaussFullL2Residual_ae
#print axioms actualOriginalGaussFullL2Residual_norm_sq_eq_integral
#check @actualOriginalGaussFullL2Residual_norm_sq_eq_integral

end
end FCP.BFSSSU2PhysicalDomainL6H5E7B
