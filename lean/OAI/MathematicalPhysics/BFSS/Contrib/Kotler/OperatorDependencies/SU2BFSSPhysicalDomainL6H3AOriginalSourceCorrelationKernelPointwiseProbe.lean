import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H2UActualOriginalSU2AbstractDominatedIntegralProbe

/-!
L6H3A — first independently qualified concrete-source correlation step
after #239/#241/#242 runner shutdowns in monolithic L6H3.

Define the precise original smooth SU(2) complex Fock inner
correlation kernel. Prove separately and explicitly:
(1) the same squared radial envelope bounds its complex norm,
(2) its original boson-variable section is continuous,
(3) its SU(2)-parameter section is continuous.

These ARE ACTUAL BFSS original smooth-core gauge orbit results, not
a replacement representation. They are necessary pointwise inputs
for the already qualified abstract L6H2U dominated integral lemma.

Intentional checkpoint: no big concrete Bochner continuity
application or FullL2 transport in this module; those remain open
until these exact source-specific leaves separately qualify.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 300000

namespace FCP.BFSSSU2PhysicalDomainL6H3A
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H0
open FCP.BFSSSU2PhysicalDomainL6H1
open MeasureTheory

/-- Exact ORIGINAL SU(2) smooth-core correlation, with source
bosonic inverse action and literal Fock fermion isometry. -/
def actualOriginalSourceGaugeCorrelationKernel
    (f : SmoothCore 2) (h g : GaugeGroup 2) (x : Boson 2) : ℂ :=
  inner ℂ (actualOriginalSmoothGaugeOrbitRepresentative f g x)
    (actualOriginalSmoothGaugeOrbitRepresentative f h x)

/-- Same H1 gauge-independent support and amplitude bounds
automatically dominate the absolute value of the complex source
correlation by the SQUARED envelope, for all g,h and positions. -/
theorem actualOriginalSourceGaugeCorrelationKernel_norm_le
    (f : SmoothCore 2) (R C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (g : GaugeGroup 2) (x : Boson 2),
      ‖actualOriginalSmoothGaugeOrbitRepresentative f g x‖ ≤
        if ‖x‖ < R then C else 0)
    (g h : GaugeGroup 2) (x : Boson 2) :
    ‖actualOriginalSourceGaugeCorrelationKernel f h g x‖ ≤
      (if ‖x‖ < R then C else 0) ^ 2 := by
  let E : ℝ := if ‖x‖ < R then C else 0
  have hE : 0 ≤ E := by
    dsimp [E]
    split_ifs <;> positivity
  change ‖inner ℂ (actualOriginalSmoothGaugeOrbitRepresentative f g x)
    (actualOriginalSmoothGaugeOrbitRepresentative f h x)‖ ≤ E ^ 2
  calc
    _ ≤ ‖actualOriginalSmoothGaugeOrbitRepresentative f g x‖ *
          ‖actualOriginalSmoothGaugeOrbitRepresentative f h x‖ :=
      norm_inner_le_norm _ _
    _ ≤ E * E := by
      apply mul_le_mul (hbound g x) (hbound h x)
      · exact norm_nonneg _
      · exact hE
    _ = E ^ 2 := by ring

/-- Native original bosonic position-section continuity. -/
theorem actualOriginalSourceGaugeCorrelationKernel_continuous_x
    (f : SmoothCore 2) (h g : GaugeGroup 2) :
    Continuous (fun x : Boson 2 =>
      actualOriginalSourceGaugeCorrelationKernel f h g x) := by
  have hsection (k : GaugeGroup 2) :
      Continuous (fun x : Boson 2 =>
        actualOriginalSmoothGaugeOrbitRepresentative f k x) := by
    have hp : Continuous (fun x : Boson 2 => (k, x)) :=
      continuous_const.prodMk continuous_id
    have ht := (actualOriginalSmoothGaugeOrbit_jointContinuous f).comp hp
    change Continuous (fun x : Boson 2 =>
      actualOriginalSmoothGaugeOrbitRepresentative f k x) at ht
    exact ht
  change Continuous (fun x : Boson 2 =>
    inner ℂ (actualOriginalSmoothGaugeOrbitRepresentative f g x)
      (actualOriginalSmoothGaugeOrbitRepresentative f h x))
  exact (hsection g).inner (hsection h)

/-- Native original SU(2) parameter-section continuity. -/
theorem actualOriginalSourceGaugeCorrelationKernel_continuous_g
    (f : SmoothCore 2) (h : GaugeGroup 2) (x : Boson 2) :
    Continuous (fun g : GaugeGroup 2 =>
      actualOriginalSourceGaugeCorrelationKernel f h g x) := by
  change Continuous (fun g : GaugeGroup 2 =>
    inner ℂ (actualOriginalSmoothGaugeOrbitRepresentative f g x)
      (actualOriginalSmoothGaugeOrbitRepresentative f h x))
  exact (actualOriginalSmoothGaugeOrbit_parameterContinuous f x).inner continuous_const

/-- Real source correlation kernels are AEStronglyMeasurable
in the ORIGINAL bosonic volume, for every pair of SU(2) elements. -/
theorem actualOriginalSourceGaugeCorrelationKernel_aeMeasurable
    (f : SmoothCore 2) (h g : GaugeGroup 2) :
    AEStronglyMeasurable
      (actualOriginalSourceGaugeCorrelationKernel f h g)
      (volume : Measure (Boson 2)) :=
  (actualOriginalSourceGaugeCorrelationKernel_continuous_x f h g).aestronglyMeasurable

#print axioms actualOriginalSourceGaugeCorrelationKernel
#print axioms actualOriginalSourceGaugeCorrelationKernel_norm_le
#print axioms actualOriginalSourceGaugeCorrelationKernel_continuous_x
#print axioms actualOriginalSourceGaugeCorrelationKernel_continuous_g
#print axioms actualOriginalSourceGaugeCorrelationKernel_aeMeasurable
#check @actualOriginalSourceGaugeCorrelationKernel_norm_le

end
end FCP.BFSSSU2PhysicalDomainL6H3A
