import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H4COriginalFullL2GaugeStrongContinuityProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7BOriginalPlusIGaugeCurveGroupLawProbe

/-!
L6H5A — native original BFSS SU(2) color curves produce genuine
strongly continuous one-parameter unitary groups on the FULL L2 space.

The literal source curve g_c(t)=exp(t • (i • pairedAlgebraData.color c))
lies in GaugeGroup 2, uses the original +i source convention and has
the qualified real-additive group law (L6G7B). The genuine FullL2
source gauge representation U(g) has qualified group law and all-vector
strong continuity (L6G7Y, H4C). The only additional analytic bridge
is the parameter continuity of the pinned matrix exponential as a
map into the ACTUAL special unitary subgroup, proved using the exact
pinned normed-algebra exponential and subtype topology.

No extra assumption, surrogate operator, generator-domain conclusion,
strong differentiability, or spectral claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5A
noncomputable section

open scoped Matrix.Norms.L2Operator
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2PhysicalDomainL6G6V
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7B
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6G7Y
open FCP.BFSSSU2PhysicalDomainL6H4C

/-- The EXACT original source positive-i SU(2) gauge curve
is continuous in the genuine subgroup topology, not merely
as an ambient color matrix. -/
theorem sourcePlusIGaugeCurve_continuous (c : ColorIndex 2) :
    Continuous (sourcePlusIGaugeCurve c) := by
  let : NormedAlgebra ℚ (ColorMatrix 2) :=
    .restrictScalars ℚ ℂ (ColorMatrix 2)
  have harg :
      Continuous (fun t : ℝ =>
        t • ((Complex.I : ℂ) • pairedAlgebraData.color c)) :=
    continuous_id.smul continuous_const
  have hexp : Continuous (sourcePlusIColorMatrix c) := by
    change Continuous (fun t : ℝ =>
      NormedSpace.exp (t • ((Complex.I : ℂ) • pairedAlgebraData.color c)))
    exact NormedSpace.exp_continuous.comp harg
  have hsub :
      Continuous (fun t : ℝ =>
        (⟨sourcePlusIColorMatrix c t,
          sourcePlusIColorMatrix_mem_specialUnitary c t⟩ : GaugeGroup 2)) :=
    hexp.subtype_mk (sourcePlusIColorMatrix_mem_specialUnitary c)
  exact hsub

/-- True source-defined FullL2 gauge orbit is norm-continuous in
real time along the actual +i SU(2) one-parameter color subgroup. -/
theorem actualOriginalFullL2ColorCurve_orbit_continuous
    (c : ColorIndex 2) (v : FullL2 2) :
    Continuous (fun t : ℝ =>
      actualOriginalFullL2GaugePairCLM (sourcePlusIGaugeCurve c t) v) :=
  (actualOriginalFullL2GaugePair_orbit_continuous v).comp
    (sourcePlusIGaugeCurve_continuous c)

/-- The actual FullL2 source unitary gauge maps obey the EXACT
real-time additive group law with no alternative Fock action. -/
theorem actualOriginalFullL2ColorCurve_add
    (c : ColorIndex 2) (s t : ℝ) (v : FullL2 2) :
    actualOriginalFullL2GaugePairCLM (sourcePlusIGaugeCurve c (s + t)) v =
      actualOriginalFullL2GaugePairCLM (sourcePlusIGaugeCurve c s)
        (actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c t) v) := by
  rw [sourcePlusIGaugeCurve_add]
  exact (actualOriginalFullL2GaugePair_mul
    (sourcePlusIGaugeCurve c s) (sourcePlusIGaugeCurve c t) v).symm

/-- The genuine source one-parameter unitary group starts at
the identity operator on the entire original FullL2 space. -/
theorem actualOriginalFullL2ColorCurve_zero
    (c : ColorIndex 2) (v : FullL2 2) :
    actualOriginalFullL2GaugePairCLM (sourcePlusIGaugeCurve c 0) v = v := by
  rw [sourcePlusIGaugeCurve_one]
  exact actualOriginalFullL2GaugePair_one v

#print axioms sourcePlusIGaugeCurve_continuous
#print axioms actualOriginalFullL2ColorCurve_orbit_continuous
#print axioms actualOriginalFullL2ColorCurve_add
#print axioms actualOriginalFullL2ColorCurve_zero
#check @actualOriginalFullL2ColorCurve_orbit_continuous

end
end FCP.BFSSSU2PhysicalDomainL6H5A
