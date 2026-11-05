import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B25WeightedFormDomainExactnessProbe
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# BFSS SU(2) D2B26 — source physical weak-form associated operator, exact 1/16

PROSPECTIVE until pinned Lean 4.34.1 CI+axioms gate is GREEN.

The original source charge T : G.physicalSpace → SourceChargeHilbertOutput
is closed and densely defined, its actual Hilbert adjoint T† and the
literal natural-domain product T†T have been kernel-verified.

The exact normalized weak-form associated-vector condition is:

   ∀v∈Dom(T), ⟪w,v⟫ = (1/16) ⟪Tu,Tv⟫

and is equivalent to ψ∈Dom(T†T) with w=(1/16)T†T ψ.

The abstract Hilbert-adjoint representation step reuses the *pinned*
Mathlib LinearPMap.mem_adjoint_domain_of_exists / adjoint_apply_eq
API, not any external theorem or new physical dynamics.

This is source-operator identification of the normalized polarized
closed form. A separately proved abstract manuscript gauge intertwiner
or positive spectral theorem is NOT claimed.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B26
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2B17
open FCP.BFSSSU2PhysicalDomainD2B18
open FCP.BFSSSU2PhysicalDomainD2B19
open FCP.BFSSSU2PhysicalDomainD2B21
open FCP.BFSSSU2PhysicalDomainD2B25

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Exact Riesz/adjoint characterization already supported by pinned
Mathlib: no new functional-analytic hypothesis, no invented operator. -/
theorem weakRepresentative_iff_adjoint
    (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E))
    (y : F) (w : E) :
    (∀ v : T.domain, inner ℂ w (v : E) = inner ℂ y (T v)) ↔
      ∃ hy : y ∈ T.adjoint.domain, w = T.adjoint ⟨y, hy⟩ := by
  constructor
  · intro hw
    have hy : y ∈ T.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists y ⟨w, hw⟩
    refine ⟨hy, ?_⟩
    exact (LinearPMap.adjoint_apply_eq hd ⟨y, hy⟩ hw).symm
  · rintro ⟨hy, rfl⟩
    exact LinearPMap.adjoint_isFormalAdjoint hd ⟨y, hy⟩

/-- A weak representative exists iff the ORIGINAL input lies in the
literal natural domain of the source adjoint-square. -/
theorem weakRepresentative_iff_naturalAdjointSquare
    (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E))
    (u : T.domain) (w : E) :
    (∀ v : T.domain,
      inner ℂ w (v : E) = inner ℂ (T u) (T v)) ↔
      ∃ h : (u : E) ∈ (naturalComp T.adjoint T).domain,
        w = naturalComp T.adjoint T ⟨u, h⟩ := by
  rw [weakRepresentative_iff_adjoint T hd (T u) w]
  constructor
  · rintro ⟨ht, hw⟩
    have hu : (u : E) ∈ (naturalComp T.adjoint T).domain :=
      naturalComp_mem_domain.mpr ⟨u.property, ht⟩
    refine ⟨hu, ?_⟩
    rw [naturalComp_apply]
    exact hw
  · rintro ⟨hu, hw⟩
    have ht : T u ∈ T.adjoint.domain :=
      naturalComp_apply_mem (⟨u, hu⟩ :
        (naturalComp T.adjoint T).domain)
    refine ⟨ht, ?_⟩
    rw [naturalComp_apply] at hw
    exact hw

/-- Positive REAL coefficient 16 acts as expected in the
conjugate-linear first slot of the complex Hilbert inner product. -/
theorem sixteen_inner_smul (x y : E) :
    inner ℂ ((16 : ℂ) • x) y = (16 : ℂ) * inner ℂ x y := by
  rw [inner_smul_left]
  simp only [map_ofNat]

/-- Exactly 1/16 in the complex inner product's conjugate-linear
slot; this normalization may not be replaced by a convention. -/
theorem one_sixteenth_inner_smul (x y : E) :
    inner ℂ ((1 / 16 : ℂ) • x) y =
      (1 / 16 : ℂ) * inner ℂ x y := by
  rw [inner_smul_left]
  simp only [map_div₀, map_one, map_ofNat]

/-- The source-independent associated-operator identity on the
exact natural domain, with the paper's factor 1/16. -/
theorem normalizedWeakRepresentative_iff_naturalAdjointSquare
    (T : E →ₗ.[ℂ] F) (hd : Dense (T.domain : Set E))
    (u : T.domain) (w : E) :
    (∀ v : T.domain,
      inner ℂ w (v : E) =
        (1 / 16 : ℂ) * inner ℂ (T u) (T v)) ↔
      ∃ h : (u : E) ∈ (naturalComp T.adjoint T).domain,
        w = (1 / 16 : ℂ) • (naturalComp T.adjoint T ⟨u, h⟩) := by
  constructor
  · intro hw
    have h16 : ∀ v : T.domain,
        inner ℂ ((16 : ℂ) • w) (v : E) =
          inner ℂ (T u) (T v) := by
      intro v
      rw [sixteen_inner_smul, hw v]
      ring
    obtain ⟨hu, hw16⟩ :=
      (weakRepresentative_iff_naturalAdjointSquare T hd u
        ((16 : ℂ) • w)).mp h16
    refine ⟨hu, ?_⟩
    have heq := congrArg ((1 / 16 : ℂ) • ·) hw16
    have hcancel : (1 / 16 : ℂ) • ((16 : ℂ) • w) = w := by
      rw [smul_smul]
      norm_num
    exact hcancel.symm.trans heq
  · rintro ⟨hu, hw⟩
    have hweak :
        ∀ v : T.domain,
          inner ℂ (naturalComp T.adjoint T ⟨u, hu⟩) (v : E) =
            inner ℂ (T u) (T v) :=
      (weakRepresentative_iff_naturalAdjointSquare T hd u
        (naturalComp T.adjoint T ⟨u, hu⟩)).mpr ⟨hu, rfl⟩
    intro v
    rw [hw, one_sixteenth_inner_smul, hweak v]

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- The ACTUAL pinned N=2 source physical charge closed form's
representing-vector condition is equivalent to the natural domain
of its actual Hilbert adjoint-square, with the exact coefficient. -/
theorem sourcePhysicalNormalizedWeakForm_associatedOperator_iff
    (u : (sourcePhysicalHilbertChargeColumn M G).domain)
    (w : G.physicalSpace) :
    (∀ v : (sourcePhysicalHilbertChargeColumn M G).domain,
      inner ℂ w (v : G.physicalSpace) =
        (1 / 16 : ℂ) *
          inner ℂ (sourcePhysicalHilbertChargeColumn M G u)
            (sourcePhysicalHilbertChargeColumn M G v)) ↔
      ∃ h : (u : G.physicalSpace) ∈
          (sourcePhysicalChargeAdjointSquare M G).domain,
        w = (1 / 16 : ℂ) •
          (sourcePhysicalChargeAdjointSquare M G ⟨u, h⟩) := by
  let : CompleteSpace G.physicalSpace :=
    sourceOriginalPhysicalHilbert_complete M G
  exact normalizedWeakRepresentative_iff_naturalAdjointSquare
    (sourcePhysicalHilbertChargeColumn M G)
    (sourcePhysicalHilbertChargeColumn_domain_dense M G) u w

#print axioms weakRepresentative_iff_adjoint
#print axioms weakRepresentative_iff_naturalAdjointSquare
#print axioms sixteen_inner_smul
#print axioms one_sixteenth_inner_smul
#print axioms normalizedWeakRepresentative_iff_naturalAdjointSquare
#print axioms sourcePhysicalNormalizedWeakForm_associatedOperator_iff

end
end FCP.BFSSSU2PhysicalDomainD2B26
