import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B24WeightedClosedFormGraphProbe

/-!
# BFSS SU(2) D2B25 — weighted form graph exactly exhausts true source domain

PROSPECTIVE until exact pinned CI Lean 4.34.1 axioms PASS.

D2B24 established closedness and Hilbert completeness of the weighted
source charge graph and exact form norm on every original Dom(T) state.
Show the converse: ALL points of this complete Hilbert weighted graph
arise from one original physical charge-domain state, with no
additional or missing operator domain.

The resulting embedding is a bijection that identifies the graph's
Hilbert norm with the exact source 1/16-normalized form norm.
This is the explicit complete weighted Hilbert model of the closed form.
It is not yet the form-associated operator representation theorem,
nor a literal equivalence to the separate manuscript gauge model.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B25
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2B17
open FCP.BFSSSU2PhysicalDomainD2B22
open FCP.BFSSSU2PhysicalDomainD2B23
open FCP.BFSSSU2PhysicalDomainD2B24

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- The ORIGINAL physical source charge domain embeds into the
COMPLETE weighted Hilbert graph from D2B24. -/
noncomputable def sourcePhysicalFormDomainIntoWeightedGraph
    (u : (sourcePhysicalHilbertChargeColumn M G).domain) :
      sourcePhysicalWeightedFormGraph M G :=
  ⟨WithLp.toLp 2 ((u : G.physicalSpace),
      (1 / 4 : ℂ) • sourcePhysicalHilbertChargeColumn M G u),
    sourcePhysicalWeightedFormGraph_contains M G u⟩

/-- There are no EXTRA weighted graph points: every element comes
from a literal state in the original source physical charge domain. -/
theorem sourcePhysicalWeightedFormGraph_exhausted
    (p : sourcePhysicalWeightedFormGraph M G) :
    ∃ u : (sourcePhysicalHilbertChargeColumn M G).domain,
      (p : WithLp 2 (G.physicalSpace × SourceChargeHilbertOutput)) =
        WithLp.toLp 2 ((u : G.physicalSpace),
          (1 / 4 : ℂ) • sourcePhysicalHilbertChargeColumn M G u) := by
  have hp : ((WithLp.ofLp (p :
        WithLp 2 (G.physicalSpace × SourceChargeHilbertOutput))).1,
      (4 : ℂ) • (WithLp.ofLp (p :
        WithLp 2 (G.physicalSpace × SourceChargeHilbertOutput))).2) ∈
      (sourcePhysicalHilbertChargeColumn M G).graph := p.property
  obtain ⟨u, hfst, hsnd⟩ :=
    (LinearPMap.mem_graph_iff _).mp hp
  refine ⟨u, ?_⟩
  apply (WithLp.linearEquiv 2 ℂ
    (G.physicalSpace × SourceChargeHilbertOutput)).injective
  change WithLp.ofLp
      (p : WithLp 2 (G.physicalSpace × SourceChargeHilbertOutput)) =
      ((u : G.physicalSpace),
        (1 / 4 : ℂ) • sourcePhysicalHilbertChargeColumn M G u)
  apply Prod.ext
  · exact hfst.symm
  · calc
      (WithLp.ofLp (p :
        WithLp 2 (G.physicalSpace × SourceChargeHilbertOutput))).2 =
          (1 / 4 : ℂ) • ((4 : ℂ) •
            (WithLp.ofLp (p :
              WithLp 2 (G.physicalSpace × SourceChargeHilbertOutput))).2) := by
                rw [smul_smul]
                norm_num
      _ = (1 / 4 : ℂ) • sourcePhysicalHilbertChargeColumn M G u :=
        congrArg ((1 / 4 : ℂ) • ·) hsnd.symm

/-- The explicit source physical form-domain identification is
injective (no two different charge states yield the same graph point). -/
theorem sourcePhysicalFormDomainIntoWeightedGraph_injective :
    Function.Injective (sourcePhysicalFormDomainIntoWeightedGraph M G) := by
  intro u v huv
  apply Subtype.ext
  have h := congrArg
    (fun p : sourcePhysicalWeightedFormGraph M G =>
      (WithLp.ofLp (p :
        WithLp 2 (G.physicalSpace × SourceChargeHilbertOutput))).1) huv
  exact h

/-- All complete weighted graph points arise from original source
charge-domain vectors, not an invented extension. -/
theorem sourcePhysicalFormDomainIntoWeightedGraph_surjective :
    Function.Surjective (sourcePhysicalFormDomainIntoWeightedGraph M G) := by
  intro p
  obtain ⟨u, hu⟩ := sourcePhysicalWeightedFormGraph_exhausted M G p
  refine ⟨u, ?_⟩
  apply Subtype.ext
  exact hu.symm

/-- Form norm is EXACTLY the transported complete weighted Hilbert
norm; this is an equality of the accepted original source form. -/
theorem sourcePhysicalFormDomainIntoWeightedGraph_norm_sq
    (u : (sourcePhysicalHilbertChargeColumn M G).domain) :
    ‖(sourcePhysicalFormDomainIntoWeightedGraph M G u :
      WithLp 2 (G.physicalSpace × SourceChargeHilbertOutput))‖ ^ 2 =
      sourcePhysicalFormNormSq M G u :=
  sourcePhysicalWeightedFormGraph_norm_sq M G u

#print axioms sourcePhysicalWeightedFormGraph_exhausted
#print axioms sourcePhysicalFormDomainIntoWeightedGraph_injective
#print axioms sourcePhysicalFormDomainIntoWeightedGraph_surjective
#print axioms sourcePhysicalFormDomainIntoWeightedGraph_norm_sq

end
end FCP.BFSSSU2PhysicalDomainD2B25
