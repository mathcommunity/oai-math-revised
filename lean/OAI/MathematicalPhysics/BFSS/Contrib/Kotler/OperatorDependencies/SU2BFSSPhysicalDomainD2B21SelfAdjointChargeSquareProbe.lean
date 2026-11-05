import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B20VonNeumannGraphSurjectivityProbe
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# BFSS SU2 D2B21 — physical natural charge adjoint-square is genuinely self-adjoint

PROSPECTIVE until the exact pinned Actions compiler and axiom smoke PASS.

D2B19 proves formal symmetry on the correct natural operator domain.
D2B20 proves 1 + T†T maps that domain ONTO the entire physical Hilbert space.
The general Hilbert-space proof below shows these two properties imply
genuine Mathlib IsSelfAdjoint, with its actual adjoint and operator domain.

Proof method adapted to the pinned Mathlib API from Keisuke Suzuki,
QuantumSystem/Analysis/UnboundedOperator/VonNeumann.lean,
commit a2bb99fcb82c820f040004a2f99c875575c72efd (Apache-2.0).
No external dependency; no change in pinned source identities; no axioms.

Not yet claimed: exact 1/16 scaling, closed-form representation uniqueness,
the manuscript's abstract gauge intertwiner, spectral or physics results.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B21
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2B17
open FCP.BFSSSU2PhysicalDomainD2B18
open FCP.BFSSSU2PhysicalDomainD2B19
open FCP.BFSSSU2PhysicalDomainD2B20
open RCLike LinearPMap
open scoped ComplexConjugate

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

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- GENUINE self-adjointness of the exact original BFSS SU(2) physical
natural-domain T†T. The only input is the already qualified physical
symmetry and its closed-graph resolvent surjectivity. -/
theorem sourcePhysicalChargeAdjointSquare_selfAdjoint :
    letI : CompleteSpace G.physicalSpace :=
      sourceOriginalPhysicalHilbert_complete M G
    IsSelfAdjoint (sourcePhysicalChargeAdjointSquare M G) := by
  let : CompleteSpace G.physicalSpace :=
    sourceOriginalPhysicalHilbert_complete M G
  exact selfAdjoint_of_formalSymmetry_and_shift_surjectivity
    (sourcePhysicalChargeAdjointSquare M G)
    (sourcePhysicalChargeAdjointSquare_symmetric M G)
    (sourcePhysicalChargeAdjointSquare_shift_graph_surjective M G)

theorem sourcePhysicalChargeAdjointSquare_domain_dense :
    Dense ((sourcePhysicalChargeAdjointSquare M G).domain :
      Set G.physicalSpace) := by
  let : CompleteSpace G.physicalSpace :=
    sourceOriginalPhysicalHilbert_complete M G
  exact (sourcePhysicalChargeAdjointSquare_selfAdjoint M G).dense_domain

theorem sourcePhysicalChargeAdjointSquare_closed :
    (sourcePhysicalChargeAdjointSquare M G).IsClosed := by
  let : CompleteSpace G.physicalSpace :=
    sourceOriginalPhysicalHilbert_complete M G
  exact (sourcePhysicalChargeAdjointSquare_selfAdjoint M G).isClosed

#print axioms formalSymmetry_graph_pairing
#print axioms selfAdjoint_of_formalSymmetry_and_shift_surjectivity
#print axioms sourcePhysicalChargeAdjointSquare_selfAdjoint
#print axioms sourcePhysicalChargeAdjointSquare_domain_dense
#print axioms sourcePhysicalChargeAdjointSquare_closed

end
end FCP.BFSSSU2PhysicalDomainD2B21
