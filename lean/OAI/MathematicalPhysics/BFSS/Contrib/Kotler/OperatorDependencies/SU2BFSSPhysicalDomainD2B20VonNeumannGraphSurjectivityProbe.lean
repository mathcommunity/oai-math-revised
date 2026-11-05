import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B19NaturalChargeSquarePositiveProbe
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# BFSS SU2 D2B20 — von Neumann graph decomposition / resolvent-surjectivity bridge

PROSPECTIVE. Until pinned CI passes, no theorem is accepted.

For the *actual source* closed and densely defined physical charge T, show that
1 + T†T is onto the physical Hilbert space on its EXACT natural domain.
The proof uses orthogonal projection onto the closed graph of T,
not an invented invariant-domain assumption.

Adaptation of a general argument: Keisuke Suzuki,
QuantumSystem/Analysis/UnboundedOperator/VonNeumann.lean
(commit a2bb99fcb82c820f040004a2f99c875575c72efd; Apache-2.0).
Re-verified in the pinned FCP source tree if and only if CI compiles.
No external dependency imported, no axiom introduced.

This is a significant step towards, but NOT YET, the self-adjointness
or manuscript-form representation theorem for (1/16) T†T.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B20
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2B17
open FCP.BFSSSU2PhysicalDomainD2B18
open FCP.BFSSSU2PhysicalDomainD2B19
open RCLike LinearPMap
open scoped ComplexConjugate

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The exact graph of the natural-domain product is a relational
composition of the two original graphs. -/
theorem mem_graph_naturalComp {T : E →ₗ.[ℂ] F} {A : F →ₗ.[ℂ] E}
    {x z : E} :
    (x, z) ∈ (naturalComp A T).graph ↔
      ∃ y : F, (x, y) ∈ T.graph ∧ (y, z) ∈ A.graph := by
  constructor
  · intro h
    obtain ⟨u, rfl, rfl⟩ := (LinearPMap.mem_graph_iff _).mp h
    refine ⟨T ⟨u, naturalComp_domain_le u.property⟩, ?_, ?_⟩
    · exact T.mem_graph ⟨u, naturalComp_domain_le u.property⟩
    · rw [naturalComp_apply]
      exact A.mem_graph
        ⟨T ⟨u, naturalComp_domain_le u.property⟩, naturalComp_apply_mem u⟩
  · rintro ⟨y, hy, hz⟩
    obtain ⟨u, rfl, rfl⟩ := (LinearPMap.mem_graph_iff _).mp hy
    obtain ⟨v, hv, hzv⟩ := (LinearPMap.mem_graph_iff _).mp hz
    change (v : F) = T u at hv
    have hTv : T u ∈ A.domain := by
      rw [← hv]
      exact v.property
    have hd : (u : E) ∈ (naturalComp A T).domain :=
      naturalComp_mem_domain.mpr ⟨u.property, hTv⟩
    refine (LinearPMap.mem_graph_iff _).mpr ⟨⟨u, hd⟩, rfl, ?_⟩
    rw [naturalComp_apply]
    exact (congrArg A (Subtype.ext hv.symm)).trans hzv

/-- Source-independent von Neumann graph decomposition for the natural
T†T domain. No full-domain composition hypothesis enters. -/
theorem naturalAdjointSquare_shift_graph_surjective
    (T : E →ₗ.[ℂ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (h : E) :
    ∃ x z : E, (x, z) ∈ (naturalComp T.adjoint T).graph ∧ x + z = h := by
  let G : Submodule ℂ (WithLp 2 (E × F)) :=
    T.graph.comap (WithLp.linearEquiv 2 ℂ (E × F)).toLinearMap
  have hG : _root_.IsClosed (G : Set (WithLp 2 (E × F))) :=
    hT.preimage (WithLp.prod_continuous_ofLp 2 E F)
  have : CompleteSpace G := hG.completeSpace_coe
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    G.exists_add_mem_mem_orthogonal (WithLp.toLp 2 (h, 0))
  have hpq' := congrArg WithLp.ofLp hpq
  simp only [WithLp.ofLp_add, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at hpq'
  have hq' : ∀ a b, (a, b) ∈ T.graph →
      inner ℂ a (WithLp.ofLp q).1 + inner ℂ b (WithLp.ofLp q).2 = 0 := by
    intro a b hab
    have h₁ := (Submodule.mem_orthogonal _ _).mp hq (WithLp.toLp 2 (a, b)) hab
    rwa [WithLp.prod_inner_apply, WithLp.ofLp_toLp] at h₁
  have hba : ((WithLp.ofLp q).2, -(WithLp.ofLp q).1) ∈ T.adjoint.graph := by
    rw [LinearPMap.adjoint_graph_eq_graph_adjoint hd, Submodule.mem_adjoint_iff]
    intro a b hab
    rw [inner_neg_right, sub_neg_eq_add, add_comm]
    exact hq' a b hab
  have hya : ((WithLp.ofLp p).2, (WithLp.ofLp q).1) ∈ T.adjoint.graph := by
    have hneg := T.adjoint.graph.neg_mem hba
    rwa [Prod.neg_mk, neg_neg, ← eq_neg_of_add_eq_zero_left hpq'.2.symm] at hneg
  exact ⟨_, _, mem_graph_naturalComp.mpr ⟨_, hp, hya⟩, hpq'.1.symm⟩

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- Every physical Hilbert vector is in the range of 1 + T†T,
using the exact BFSS source-defined charge and its true Hilbert adjoint. -/
theorem sourcePhysicalChargeAdjointSquare_shift_graph_surjective
    (h : G.physicalSpace) :
    ∃ x z : G.physicalSpace,
      (x, z) ∈ (sourcePhysicalChargeAdjointSquare M G).graph ∧ x + z = h := by
  let : CompleteSpace G.physicalSpace :=
    sourceOriginalPhysicalHilbert_complete M G
  exact naturalAdjointSquare_shift_graph_surjective
    (sourcePhysicalHilbertChargeColumn M G)
    (sourcePhysicalHilbertChargeColumn_isClosed M G)
    (sourcePhysicalHilbertChargeColumn_domain_dense M G) h

#print axioms mem_graph_naturalComp
#print axioms naturalAdjointSquare_shift_graph_surjective
#print axioms sourcePhysicalChargeAdjointSquare_shift_graph_surjective

end
end FCP.BFSSSU2PhysicalDomainD2B20
