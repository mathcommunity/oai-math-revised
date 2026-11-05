import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B13OriginalSmoothCoreChargeGraphClosureProbe

/-!
# BFSS SU2 D2B14 — exact closed physical charge energy on its true source domain

PROSPECTIVE / UNCOMPILED until the pinned Actions gate succeeds.

The energy is the literal sum of squared norms of the ACTUAL D2B12
closed gauge-restricted source charge operator, at the source 1/16
normalization. It is defined only on that operator's actual domain.

Its restriction to the ORIGINAL invariant SmoothCore agrees exactly
with M.coreForm, and hence with the accepted original massless
deformedCoreEnergy 1 0. This is the necessary initial form-domain
bridge, not yet an associated self-adjoint Hamiltonian theorem.

The source raw-core-to-closed charge graph identity is preserved.
No graph-dominance or maximum differential realization is assumed.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B14
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG4K9D
open FCP.BFSSSU2PhysicalDomainD2B11
open FCP.BFSSSU2PhysicalDomainD2B12
open Finset MeasureTheory Set

variable {N : ℕ} (M : AlgebraData N) (G : M.GaugeData)

/-- Exact source-typed closed nonnegative charge quadratic energy.
The actual source physical charge operator domain is the form domain.
Do not replace this with the full-space charge graph or norm closure. -/
noncomputable def sourceClosedPhysicalChargeEnergy
    (u : (sourceClosedPhysicalChargeColumn M G).domain) : ℝ :=
  (1 / 16 : ℝ) * ∑ α : SpinIndex,
    ‖(sourceClosedPhysicalChargeColumn M G u) α‖ ^ 2

/-- Nonnegativity follows componentwise from the actual closed
operator output; there is no assumed positivity of a Hamiltonian. -/
theorem sourceClosedPhysicalChargeEnergy_nonneg
    (u : (sourceClosedPhysicalChargeColumn M G).domain) :
    0 ≤ sourceClosedPhysicalChargeEnergy M G u := by
  unfold sourceClosedPhysicalChargeEnergy
  apply mul_nonneg
  · norm_num
  · exact Finset.sum_nonneg (fun α hα => sq_nonneg _)

/-- Every exact original source gauge-invariant smooth test section
lies in the domain of the true closed physical charge column. -/
noncomputable def sourceCoreInClosedChargeDomain
    (f : G.invariantCore) :
    (sourceClosedPhysicalChargeColumn M G).domain :=
  ⟨coreToL2 f.val, by
    apply LinearPMap.mem_domain_of_mem_graph
    rw [sourceClosedPhysicalChargeColumn_graph_eq M G]
    exact sourceRestrictedPhysicalGraph_containsCore M G f⟩

/-- On any literal original source invariant smooth section,
the closed charge operator acts by the ORIGINAL source chargeVector,
not just by some extension whose core action is unidentified. -/
theorem sourceClosedChargeColumn_on_sourceCore (f : G.invariantCore) :
    sourceClosedPhysicalChargeColumn M G
      (sourceCoreInClosedChargeDomain M G f) =
      M.chargeVector f.val := by
  have hsource :
      (coreToL2 f.val, M.chargeVector f.val) ∈
        (sourceClosedPhysicalChargeColumn M G).graph := by
    rw [sourceClosedPhysicalChargeColumn_graph_eq M G]
    exact sourceRestrictedPhysicalGraph_containsCore M G f
  have hoperator :
      ((sourceCoreInClosedChargeDomain M G f : FullL2 N),
        sourceClosedPhysicalChargeColumn M G
          (sourceCoreInClosedChargeDomain M G f)) ∈
        (sourceClosedPhysicalChargeColumn M G).graph :=
    (sourceClosedPhysicalChargeColumn M G).mem_graph _
  exact (sourceClosedPhysicalChargeColumn M G).mem_graph_snd_inj
    hoperator hsource rfl

/-- The closed-domain energy agrees EXACTLY with the original upstream
coreForm (sixteen charges and the original 1/16 normalization).
This bridges the newly closed operator with the actual original
kinematical BFSS quadratic energy, without an assumed form identity. -/
theorem sourceClosedPhysicalChargeEnergy_on_sourceCore_eq_coreForm
    (f : G.invariantCore) :
    sourceClosedPhysicalChargeEnergy M G
      (sourceCoreInClosedChargeDomain M G f) =
      M.coreForm f.val := by
  unfold sourceClosedPhysicalChargeEnergy
  rw [sourceClosedChargeColumn_on_sourceCore M G f]
  rfl

/-- The true closed-domain energy on the invariant core is equally
the genuine pinned source deformed energy at exactly h=1,m=0. -/
theorem sourceClosedPhysicalChargeEnergy_on_sourceCore_eq_massless
    (f : G.invariantCore) :
    sourceClosedPhysicalChargeEnergy M G
      (sourceCoreInClosedChargeDomain M G f) =
      M.deformedCoreEnergy 1 0 f.val := by
  rw [sourceClosedPhysicalChargeEnergy_on_sourceCore_eq_coreForm M G f]
  exact (sourceUnconditionalCoreForm_equal M f.val).symm

#print axioms sourceClosedPhysicalChargeEnergy_nonneg
#print axioms sourceClosedChargeColumn_on_sourceCore
#print axioms sourceClosedPhysicalChargeEnergy_on_sourceCore_eq_coreForm
#print axioms sourceClosedPhysicalChargeEnergy_on_sourceCore_eq_massless

end
end FCP.BFSSSU2PhysicalDomainD2B14
