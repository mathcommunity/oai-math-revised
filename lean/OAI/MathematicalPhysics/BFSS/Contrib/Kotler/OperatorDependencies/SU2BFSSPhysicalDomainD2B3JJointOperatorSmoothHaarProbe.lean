import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B3SmoothHaarReductionProbe

/-!
# BFSS SU(2) D2B3J — TRUE SOURCE OPERATOR-PARAMETER JOINT SMOOTHNESS

PROSPECTIVE / UNCOMPILED until the exact pinned CI gate passes.

Crucial strategy: do not expand high-order derivatives of the
huge original Fermion 2 object. Instead realize the real
source gauge representations as continuously varying
bounded real-linear operators, apply the existing pinned
`OAI.RVM.SmoothCompactFamily.ofJoint` theorem, and then
discharge the ACTUAL all-jet continuity hypothesis of D2B3.

No new GaugeData axioms, substitute group action, abstract
physics object, or assumed jet/smoothness property.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B3J
noncomputable section
open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open OAI.Laughlin.Rotation
open FCP.BFSSSU2PhysicalDomainD2B1
open FCP.BFSSSU2PhysicalDomainD2B2
open FCP.BFSSSU2PhysicalDomainD2B3
open MeasureTheory
open scoped Topology ContDiff

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- The ACTUAL source boson representation, inverted in SU2, varies
continuously in the operator-norm topology. This follows from the
original joint action continuity and finite-dimensionality of Boson 2. -/
theorem sourceBosonOperator_continuous :
    Continuous (fun g : GaugeGroup 2 =>
      (G.boson g⁻¹).toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro x
  change Continuous (fun g : GaugeGroup 2 => G.boson g⁻¹ x)
  exact G.boson_continuous.comp (continuous_inv.prodMk continuous_const)

/-- The ACTUAL source complex fermion representation, restricted to
real scalars, varies continuously in real operator-norm topology.
Finite-dimensionality of the original EuclideanSpace ℂ is used,
not an approximating fermion representation. -/
theorem sourceFermionOperator_continuous :
    Continuous (fun g : GaugeGroup 2 =>
      ((G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)) := by
  apply continuous_clm_apply.mpr
  intro v
  change Continuous (fun g : GaugeGroup 2 => G.fermion g v)
  exact G.fermion_continuous.comp (continuous_id.prodMk continuous_const)

/-- The ACTUAL gauge integrand is a smooth family over compact SU2:
each spatial slice is C∞ and every spatial iterated derivative
is jointly continuous with the source gauge element. -/
theorem sourceHaarIntegrand_smoothFamily (f : SmoothCore 2) :
    OAI.RVM.SmoothCompactFamily
      (fun g : GaugeGroup 2 => fun x : Boson 2 =>
        G.fermion g (f (G.boson g⁻¹ x))) := by
  let A : Type :=
    (Boson 2 →L[ℝ] Boson 2) × (Fermion 2 →L[ℝ] Fermion 2)
  let H : A × Boson 2 → Fermion 2 :=
    fun p => p.1.2 (f (p.1.1 p.2))
  let ι : GaugeGroup 2 → A :=
    fun g => ((G.boson g⁻¹).toContinuousLinearEquiv.toContinuousLinearMap,
      ((G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ))
  have hH : ContDiff ℝ ∞ H := by
    change ContDiff ℝ ∞
      (fun p : A × Boson 2 => p.1.2 (f (p.1.1 p.2)))
    exact (contDiff_fst.snd).clm_apply
      (f.contDiff.comp ((contDiff_fst.fst).clm_apply contDiff_snd))
  have hι : Continuous ι :=
    (sourceBosonOperator_continuous M G).prodMk
      (sourceFermionOperator_continuous M G)
  exact OAI.RVM.SmoothCompactFamily.ofJoint hH hι

/-- Discharge the previously EXPLICIT AND OPEN hJets hypothesis
unconditionally, for every natural derivative order of the
ACTUAL SU2 BFSS source integrand. -/
theorem sourceHaarAllJets_jointContinuous (f : SmoothCore 2) (n : ℕ) :
    Continuous (fun p : Boson 2 × GaugeGroup 2 =>
      iteratedFDeriv ℝ n
        (fun x : Boson 2 =>
          G.fermion p.2 (f (G.boson p.2⁻¹ x))) p.1) :=
  (sourceHaarIntegrand_smoothFamily M G f).2 n

/-- UNCONDITIONAL smoothness of the original source-defined
fermion-valued SU2 Haar average, if this file compiles.
The proof uses the exact ACCEPTED D2B3 conditional theorem
with its remaining hypothesis now discharged above. -/
theorem sourceHaarAverageRaw_contDiff (f : SmoothCore 2) :
    ContDiff ℝ ∞ (sourceHaarAverageRaw M G f) :=
  sourceHaarAverageRaw_contDiff_of_jointJets M G f
    (sourceHaarAllJets_jointContinuous M G f)

#print axioms sourceBosonOperator_continuous
#print axioms sourceFermionOperator_continuous
#print axioms sourceHaarIntegrand_smoothFamily
#print axioms sourceHaarAllJets_jointContinuous
#print axioms sourceHaarAverageRaw_contDiff

end
end FCP.BFSSSU2PhysicalDomainD2B3J
