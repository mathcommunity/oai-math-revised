import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8BCOriginalPhysicalChargeNaturalAdjointSquareProbe
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# H5E8BD — original SU2 physical Hilbert natural T†T self-adjointness

PROSPECTIVE: NOT KERNEL-QUALIFIED until exact pinned Lean + axiom gate.

Use the actual AY/BB original sixteen-charge T and T†, and BC's
natural-domain, formally symmetric and positive product. Prove its
graph-projection/resolvent criterion and genuine Mathlib IsSelfAdjoint.
No full-domain invariance assumption, deformed-model source alias,
unproved physics axiom or imported historical operator is introduced.

The general Hilbert graph results are adapted locally from the
historically accepted FCP D2B20/D2B21 exact-source proofs.
Historical attribution: Keisuke Suzuki, QuantumSystem/
Analysis/UnboundedOperator/VonNeumann.lean,
commit a2bb99fcb82c820f040004a2f99c875575c72efd (Apache-2.0).

Self-adjoint T†T does not by itself identify the normalized (1/16)
source closed-form Hamiltonian, the independent manuscript
Cl(48)/Spin(48) gauge intertwiner, positive spectrum or mass gap.
-/

set_option autoImplicit false
set_option maxHeartbeats 250000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8BD
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open FCP.BFSSSU2PhysicalDomainL6H5E8BA
open FCP.BFSSSU2PhysicalDomainL6H5E8BB
open FCP.BFSSSU2PhysicalDomainL6H5E8BC
open RCLike LinearPMap
open scoped ComplexConjugate

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

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
theorem originalMinimalPhysicalHilbertChargeAdjointSquare_shift_graph_surjective
    (h : G.physicalSpace) :
    ∃ x z : G.physicalSpace,
      (x, z) ∈ (originalMinimalPhysicalHilbertChargeAdjointSquare M G).graph ∧ x + z = h := by
  letI : CompleteSpace G.physicalSpace :=
    originalPhysicalHilbertComplete M G
  exact naturalAdjointSquare_shift_graph_surjective
    (originalMinimalPhysicalHilbertChargeColumn M G)
    (originalMinimalPhysicalHilbertChargeColumn_isClosed M G)
    (originalMinimalPhysicalHilbertChargeColumn_domain_dense_unconditional M G) h



variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A formally symmetric unbounded operator has the symmetry identity
on any two graph points. Not an unverified imported lemma. -/
theorem formalSymmetry_graph_pairing (A : E →ₗ.[ℂ] E)
    (hA : A.IsFormalAdjoint A) {a b u v : E}
    (hab : (a, b) ∈ A.graph) (huv : (u, v) ∈ A.graph) :
    inner ℂ b u = inner ℂ a v := by
  obtain ⟨p, rfl, rfl⟩ := (LinearPMap.mem_graph_iff _).mp hab
  obtain ⟨q, rfl, rfl⟩ := (LinearPMap.mem_graph_iff _).mp huv
  exact hA p q

/-- Hilbert-space von Neumann criterion for a symmetric partial operator:
surjectivity of 1 + A on its actual domain forces A† = A. -/
theorem selfAdjoint_of_formalSymmetry_and_shift_surjectivity
    (A : E →ₗ.[ℂ] E) (hA : A.IsFormalAdjoint A)
    (hs : ∀ h : E, ∃ u v : E, (u, v) ∈ A.graph ∧ u + v = h) :
    IsSelfAdjoint A := by
  have hd : Dense (A.domain : Set E) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro h hh
    obtain ⟨u, v, huv, rfl⟩ := hs h
    have hu : ∀ x : E, inner ℂ x u = 0 := by
      intro x
      obtain ⟨a, b, hab, rfl⟩ := hs x
      have h₁ := (Submodule.mem_orthogonal _ _).mp hh a
        (LinearPMap.mem_domain_of_mem_graph hab)
      rw [inner_add_right, ← formalSymmetry_graph_pairing A hA hab huv] at h₁
      simpa only [inner_add_left] using h₁
    have hu0 : u = 0 := inner_self_eq_zero.mp (hu u)
    subst hu0
    rw [A.graph_fst_eq_zero_snd huv rfl, zero_add]
  rw [LinearPMap.isSelfAdjoint_def]
  refine LinearPMap.eq_of_eq_graph ?_
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hd]
  refine (le_antisymm (fun p huv => ?_) fun p hyw => ?_).symm
  · obtain ⟨u, v⟩ := p
    rw [Submodule.mem_adjoint_iff]
    intro a b hab
    rw [formalSymmetry_graph_pairing A hA hab huv, sub_self]
  · obtain ⟨y, w⟩ := p
    rw [Submodule.mem_adjoint_iff] at hyw
    obtain ⟨u, v, huv, he⟩ := hs (y + w)
    have hperp : ∀ a b, (a, b) ∈ A.graph →
        inner ℂ (a + b) (y - u) = 0 := by
      intro a b hab
      have h₁ := hyw a b hab
      have h₂ := formalSymmetry_graph_pairing A hA hab huv
      have h₃ : inner ℂ a (u + v) = inner ℂ a (y + w) := by rw [he]
      simp only [inner_add_right] at h₃
      simp only [inner_add_left, inner_sub_right]
      linear_combination h₁ - h₂ - h₃
    have hyu : y = u := by
      obtain ⟨a, b, hab, hab'⟩ := hs (y - u)
      have hz := hperp a b hab
      rw [hab', inner_self_eq_zero, sub_eq_zero] at hz
      exact hz
    subst hyu
    obtain rfl : v = w := add_left_cancel he
    exact huv



/-- GENUINE self-adjointness of the exact original BFSS SU(2) physical
natural-domain T†T. The only input is the already qualified physical
symmetry and its closed-graph resolvent surjectivity. -/
theorem originalMinimalPhysicalHilbertChargeAdjointSquare_selfAdjoint :
    letI : CompleteSpace G.physicalSpace :=
      originalPhysicalHilbertComplete M G
    IsSelfAdjoint (originalMinimalPhysicalHilbertChargeAdjointSquare M G) := by
  letI : CompleteSpace G.physicalSpace :=
    originalPhysicalHilbertComplete M G
  exact selfAdjoint_of_formalSymmetry_and_shift_surjectivity
    (originalMinimalPhysicalHilbertChargeAdjointSquare M G)
    (originalMinimalPhysicalHilbertChargeAdjointSquare_symmetric M G)
    (originalMinimalPhysicalHilbertChargeAdjointSquare_shift_graph_surjective M G)

theorem originalMinimalPhysicalHilbertChargeAdjointSquare_domain_dense :
    Dense ((originalMinimalPhysicalHilbertChargeAdjointSquare M G).domain :
      Set G.physicalSpace) := by
  letI : CompleteSpace G.physicalSpace :=
    originalPhysicalHilbertComplete M G
  exact (originalMinimalPhysicalHilbertChargeAdjointSquare_selfAdjoint M G).dense_domain

theorem originalMinimalPhysicalHilbertChargeAdjointSquare_closed :
    (originalMinimalPhysicalHilbertChargeAdjointSquare M G).IsClosed := by
  letI : CompleteSpace G.physicalSpace :=
    originalPhysicalHilbertComplete M G
  exact (originalMinimalPhysicalHilbertChargeAdjointSquare_selfAdjoint M G).isClosed



#print axioms mem_graph_naturalComp
#print axioms naturalAdjointSquare_shift_graph_surjective
#print axioms originalMinimalPhysicalHilbertChargeAdjointSquare_shift_graph_surjective
#print axioms formalSymmetry_graph_pairing
#print axioms selfAdjoint_of_formalSymmetry_and_shift_surjectivity
#print axioms originalMinimalPhysicalHilbertChargeAdjointSquare_selfAdjoint
#print axioms originalMinimalPhysicalHilbertChargeAdjointSquare_domain_dense
#print axioms originalMinimalPhysicalHilbertChargeAdjointSquare_closed

end
end FCP.BFSSSU2PhysicalDomainL6H5E8BD
