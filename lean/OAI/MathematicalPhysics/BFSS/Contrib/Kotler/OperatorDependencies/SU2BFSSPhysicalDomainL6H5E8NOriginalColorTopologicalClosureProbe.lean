import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8MOriginalJointGaussKernelGeneratedColorGaugeSubgroupProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H4COriginalFullL2GaugeStrongContinuityProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7VActualSourceFullL2PhysicalFixedSpaceProbe
import Mathlib.Topology.Closure

/-!
H5E8N: actual source SU2 joint color Gauss kernel also fixes the
topological closure of its color-generated subgroup.
The physical-space equivalence requires an EXPLICIT dense
generation premise and does not prove that premise.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8N
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
-- Gate #332: the actual pairedGaugeData is defined in GaugeG4J.
-- Prior source modules opened this namespace; H5E8N must too.
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6G7V
open FCP.BFSSSU2PhysicalDomainL6H4C
open FCP.BFSSSU2PhysicalDomainL6H5E8E
open FCP.BFSSSU2PhysicalDomainL6H5E8M

theorem actualOriginalGaugeFixedSet_isClosed (v : FullL2 2) :
    IsClosed {g : GaugeGroup 2 |
      actualOriginalFullL2GaugePairCLM g v = v} := by
  exact isClosed_eq
    (actualOriginalFullL2GaugePair_orbit_continuous v)
    continuous_const

theorem actualOriginalJointKernel_fixed_colorClosure
    (v : FullL2 2)
    (hk : ∀ c : ColorIndex 2,
      ∃ hd : v ∈ actualOriginalColorGeneratorDomainSubmodule c,
        actualOriginalColorGeneratorLinear c ⟨v, hd⟩ = 0)
    (g : GaugeGroup 2)
    (hg : g ∈ closure
      (actualOriginalColorGeneratedSubgroup : Set (GaugeGroup 2))) :
    actualOriginalFullL2GaugePairCLM g v = v := by
  have hs :
      (actualOriginalColorGeneratedSubgroup : Set (GaugeGroup 2)) ⊆
        {h : GaugeGroup 2 | actualOriginalFullL2GaugePairCLM h v = v} := by
    intro h hh
    exact actualOriginalJointColorGaussKernel_fixed_generated v hk h hh
  exact (closure_minimal hs (actualOriginalGaugeFixedSet_isClosed v)) hg

theorem actualOriginalJointKernel_iff_colorClosureFixed
    (v : FullL2 2) :
    (∀ c : ColorIndex 2,
      ∃ hd : v ∈ actualOriginalColorGeneratorDomainSubmodule c,
        actualOriginalColorGeneratorLinear c ⟨v, hd⟩ = 0) ↔
    (∀ g : GaugeGroup 2,
      g ∈ closure (actualOriginalColorGeneratedSubgroup :
        Set (GaugeGroup 2)) →
        actualOriginalFullL2GaugePairCLM g v = v) := by
  constructor
  · intro hk g hg
    exact actualOriginalJointKernel_fixed_colorClosure v hk g hg
  · intro hf
    apply (actualOriginalJointColorGaussKernel_iff_generatedGaugeFixed v).mpr
    intro g hg
    exact hf g (subset_closure hg)

theorem actualOriginalJointKernel_iff_physical_of_dense
    (hdense : closure (actualOriginalColorGeneratedSubgroup :
      Set (GaugeGroup 2)) = Set.univ)
    (v : FullL2 2) :
    (∀ c : ColorIndex 2,
      ∃ hd : v ∈ actualOriginalColorGeneratorDomainSubmodule c,
        actualOriginalColorGeneratorLinear c ⟨v, hd⟩ = 0) ↔
    v ∈ pairedGaugeData.physicalSpace := by
  constructor
  · intro hk
    apply (actualOriginalFullL2GaugePair_fixed_iff_physical v).mp
    intro g
    have hg : g ∈ closure (actualOriginalColorGeneratedSubgroup :
        Set (GaugeGroup 2)) := by
      rw [hdense]
      trivial
    exact actualOriginalJointKernel_fixed_colorClosure v hk g hg
  · intro hp
    have hf := (actualOriginalFullL2GaugePair_fixed_iff_physical v).mpr hp
    apply (actualOriginalJointColorGaussKernel_iff_generatedGaugeFixed v).mpr
    intro g _
    exact hf g

#print axioms actualOriginalGaugeFixedSet_isClosed
#print axioms actualOriginalJointKernel_fixed_colorClosure
#print axioms actualOriginalJointKernel_iff_colorClosureFixed
#print axioms actualOriginalJointKernel_iff_physical_of_dense
#check @actualOriginalJointKernel_iff_physical_of_dense

end
end FCP.BFSSSU2PhysicalDomainL6H5E8N
