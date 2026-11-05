import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B8AFixedPointSpaceProbe

/-!
# BFSS SU2 D2B8B — true-source fermion L² parameter continuity and
# strong-continuity reduction to the original bosonic pullback

PROSPECTIVE / UNCOMPILED until exact pinned CI qualification.

The genuine finite-dimensional source fermion representation is continuous
in operator norm. The pinned Mathlib \`compLpL₂\` gives its L² lift as a
continuous family of bounded operators, without inventing a gauge action.

The full gauge orbit strong-continuity result below is CONDITIONAL on
the original bosonic pullback orbit. This condition remains unproved here.
No full-L² Haar projection or invariant-core density claim follows.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B8B
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2B6
open FCP.BFSSSU2PhysicalDomainD2B7
open FCP.BFSSSU2PhysicalDomainD2B8A
open MeasureTheory

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- The actual complex-linear fermion SU2 source representation
is continuous in finite-dimensional operator norm. -/
theorem sourceFermionComplexOperator_continuous :
    Continuous (fun g : GaugeGroup 2 =>
      (G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro w
  change Continuous (fun g : GaugeGroup 2 => G.fermion g w)
  exact G.fermion_continuous.comp (continuous_id.prodMk continuous_const)

/-- The actual original fermion action on the full BFSS L² Hilbert
space depends continuously on its SU2 parameter IN OPERATOR NORM.
The lift is built from pinned Mathlib's bounded bilinear \`compLpL₂\`. -/
theorem sourceFermionFiberCLM_parameter_continuous :
    Continuous (fun g : GaugeGroup 2 =>
      ((G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap).compLpL
        2 (volume : Measure (Boson 2))) := by
  let J : (Fermion 2 →L[ℂ] Fermion 2) →L[ℂ]
      (FullL2 2 →L[ℂ] FullL2 2) :=
    (ContinuousLinearMap.id ℂ (Fermion 2 →L[ℂ] Fermion 2)).compLpL₂
      2 (volume : Measure (Boson 2))
  have hJ : Continuous (fun g : GaugeGroup 2 =>
      J ((G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap)) :=
    J.continuous.comp (sourceFermionComplexOperator_continuous M G)
  have heq :
      (fun g : GaugeGroup 2 =>
        J ((G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap)) =
      (fun g : GaugeGroup 2 =>
        ((G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap).compLpL
          2 (volume : Measure (Boson 2))) := by
    funext g
    apply ContinuousLinearMap.ext
    intro v
    rfl
  rw [heq] at hJ
  exact hJ

/-- Genuine source fermion fiberAction is jointly continuous in
the SU2 gauge parameter and the original full-L² Hilbert vector. -/
theorem sourceFermionFiberAction_joint_continuous :
    Continuous (fun p : GaugeGroup 2 × FullL2 2 =>
      G.fiberAction p.1 p.2) := by
  have h : Continuous (fun p : GaugeGroup 2 × FullL2 2 =>
      (((G.fermion p.1).toContinuousLinearEquiv.toContinuousLinearMap).compLpL
        2 (volume : Measure (Boson 2))) p.2) :=
    ((sourceFermionFiberCLM_parameter_continuous M G).comp
      continuous_fst).clm_apply continuous_snd
  exact h

/-- The only unproved continuity input to the full original source
gauge orbit is the original bosonic L² pullback strong continuity.
This theorem isolates that exact analytical obligation rather than
silently postulating it as a property of GaugeData. -/
theorem sourceFullGaugePair_strongContinuous_of_boson
    (hboson : ∀ v : FullL2 2,
      Continuous (fun g : GaugeGroup 2 => G.bosonPullback g⁻¹ v))
    (v : FullL2 2) :
    Continuous (fun g : GaugeGroup 2 =>
      sourceFullGaugePairCLM M G g v) := by
  have h := (sourceFermionFiberAction_joint_continuous M G).comp
    (continuous_id.prodMk (hboson v))
  have heq :
      (fun g : GaugeGroup 2 => sourceFullGaugePairCLM M G g v) =
      (fun g : GaugeGroup 2 => G.fiberAction g (G.bosonPullback g⁻¹ v)) := by
    funext g
    exact sourceFullGaugePairCLM_apply M G g v
  rw [heq]
  exact h

#print axioms sourceFermionComplexOperator_continuous
#print axioms sourceFermionFiberCLM_parameter_continuous
#print axioms sourceFermionFiberAction_joint_continuous
#print axioms sourceFullGaugePair_strongContinuous_of_boson

end
end FCP.BFSSSU2PhysicalDomainD2B8B
