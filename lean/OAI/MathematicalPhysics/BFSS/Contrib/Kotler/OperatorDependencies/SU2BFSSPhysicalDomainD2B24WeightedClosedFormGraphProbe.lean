import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B23ExactFormGraphNormEquivalenceProbe
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# BFSS SU(2) D2B24 — exact weighted closed-form Hilbert graph

PROSPECTIVE until pinned Lean 4.34.1 CI and axiom smoke PASS.

The true source-defined charge T : G.physicalSpace → SourceChargeHilbertOutput
is closed, densely defined, and has exact original charge normalization
q(ψ) = (1/16) ‖Tψ‖² on Dom(T).

Build the Hilbert graph with output y := (1/4) Tψ, so its ordinary
WithLp 2 product norm square is literally ‖ψ‖² + q(ψ).
This is a continuous invertible reweighting of T's closed graph.
No substitute physics, weakened domain, extra axiom, spectral or
manuscript operator equality is introduced.

A later statement must show the weighted graph is exhausted by this
embedding of Dom(T) before formal completeness of the form-domain norm
can be claimed in full.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B24
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2B17
open FCP.BFSSSU2PhysicalDomainD2B22
open FCP.BFSSSU2PhysicalDomainD2B23

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- Closed form graph: the ORIGINAL physical charge graph pulled back
along the continuous output inverse scaling y ↦ 4y and the Hilbert
two-component WithLp representation. -/
noncomputable def sourcePhysicalWeightedFormGraph :
    Submodule ℂ (WithLp 2 (G.physicalSpace × SourceChargeHilbertOutput)) :=
  (sourcePhysicalHilbertChargeColumn M G).graph.comap
    (((LinearMap.id : G.physicalSpace →ₗ[ℂ] G.physicalSpace).prodMap
      ((4 : ℂ) • (LinearMap.id :
        SourceChargeHilbertOutput →ₗ[ℂ] SourceChargeHilbertOutput))).comp
      (WithLp.linearEquiv 2 ℂ
        (G.physicalSpace × SourceChargeHilbertOutput)).toLinearMap)

/-- The weighted graph is closed because 4-scaling and WithLp
coordinate extraction are continuous; original T is closed. -/
theorem sourcePhysicalWeightedFormGraph_isClosed :
    _root_.IsClosed (sourcePhysicalWeightedFormGraph M G :
      Set (WithLp 2 (G.physicalSpace × SourceChargeHilbertOutput))) := by
  change _root_.IsClosed
    {p : WithLp 2 (G.physicalSpace × SourceChargeHilbertOutput) |
      ((WithLp.ofLp p).1, (4 : ℂ) • (WithLp.ofLp p).2) ∈
        (sourcePhysicalHilbertChargeColumn M G).graph}
  have hconst : Continuous
      (fun _ : (G.physicalSpace × SourceChargeHilbertOutput) => (4 : ℂ)) :=
    continuous_const
  have hscale : Continuous
      (fun p : (G.physicalSpace × SourceChargeHilbertOutput) =>
        (4 : ℂ) • p.2) :=
    hconst.smul continuous_snd
  have hc : Continuous
      (fun p : (G.physicalSpace × SourceChargeHilbertOutput) =>
        (p.1, (4 : ℂ) • p.2)) :=
    continuous_fst.prodMk hscale
  exact (sourcePhysicalHilbertChargeColumn_isClosed M G).preimage
    (hc.comp (WithLp.prod_continuous_ofLp 2
      G.physicalSpace SourceChargeHilbertOutput))

/-- Exact weighted original source Hilbert graph is COMPLETE. -/
theorem sourcePhysicalWeightedFormGraph_complete :
    CompleteSpace (sourcePhysicalWeightedFormGraph M G) := by
  let : CompleteSpace G.physicalSpace :=
    sourceOriginalPhysicalHilbert_complete M G
  let : _root_.IsClosed (sourcePhysicalWeightedFormGraph M G :
      Set (WithLp 2 (G.physicalSpace × SourceChargeHilbertOutput))) :=
    sourcePhysicalWeightedFormGraph_isClosed M G
  infer_instance

/-- The literal form-domain vector embedded at output scaling 1/4
really belongs to the source-defined weighted charge graph. -/
theorem sourcePhysicalWeightedFormGraph_contains
    (u : (sourcePhysicalHilbertChargeColumn M G).domain) :
    WithLp.toLp 2 ((u : G.physicalSpace),
      (1 / 4 : ℂ) • sourcePhysicalHilbertChargeColumn M G u) ∈
      sourcePhysicalWeightedFormGraph M G := by
  change ((u : G.physicalSpace),
    (4 : ℂ) • ((1 / 4 : ℂ) • sourcePhysicalHilbertChargeColumn M G u)) ∈
      (sourcePhysicalHilbertChargeColumn M G).graph
  have hs :
      (4 : ℂ) • ((1 / 4 : ℂ) • sourcePhysicalHilbertChargeColumn M G u) =
        sourcePhysicalHilbertChargeColumn M G u := by
    rw [smul_smul]
    norm_num
  rw [hs]
  exact (sourcePhysicalHilbertChargeColumn M G).mem_graph u

/-- The natural squared Hilbert L² norm of the weighted graph point
is EXACTLY the original physical charge closed-form norm square. -/
theorem sourcePhysicalWeightedFormGraph_norm_sq
    (u : (sourcePhysicalHilbertChargeColumn M G).domain) :
    ‖WithLp.toLp 2 ((u : G.physicalSpace),
      (1 / 4 : ℂ) • sourcePhysicalHilbertChargeColumn M G u)‖ ^ 2 =
        sourcePhysicalFormNormSq M G u := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖(u : G.physicalSpace)‖ ^ 2 +
      ‖(1 / 4 : ℂ) • sourcePhysicalHilbertChargeColumn M G u‖ ^ 2 =
    sourcePhysicalFormNormSq M G u
  unfold sourcePhysicalFormNormSq sourcePhysicalHilbertChargeEnergy
  rw [norm_smul]
  have hn : ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) := by norm_num
  rw [hn]
  ring

#print axioms sourcePhysicalWeightedFormGraph_isClosed
#print axioms sourcePhysicalWeightedFormGraph_complete
#print axioms sourcePhysicalWeightedFormGraph_contains
#print axioms sourcePhysicalWeightedFormGraph_norm_sq

end
end FCP.BFSSSU2PhysicalDomainD2B24
