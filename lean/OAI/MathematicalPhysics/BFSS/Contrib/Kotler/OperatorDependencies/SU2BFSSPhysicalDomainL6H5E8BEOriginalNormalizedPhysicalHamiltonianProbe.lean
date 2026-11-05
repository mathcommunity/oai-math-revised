import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8BDOriginalPhysicalChargeAdjointSquareSelfAdjointProbe
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# H5E8BE — original SU2 physical sixteen-charge normalized associated operator

PROSPECTIVE; none of these new roots is accepted before strict Lean CI.

From source-exact, unconditionally densely defined, closed AY/BA/BB
physical sixteen-charge column T, BC/BD proved A=T†T on its natural
domain and genuine IsSelfAdjoint A. Here we reconstruct the exact
original source 1/16 normalization as a genuine Hilbert partial
operator H=(1/16)T†T; prove its unchanged domain, action, true
self-adjointness, graph closure and dense domain. Separately, prove
the precise weak-form representing-vector iff for the actual original
source 1/16 charge form against EVERY vector in Dom(T). Thus H is
the *source-original closed-charge-form associated operator*, not a
mere formal differential expression, on its exact natural domain.

The generic Hilbert adjoint Riesz/weak-form arguments are locally
requalified from FCP's accepted D2B26. Nonzero real scalar adjoint
arguments are adapted from D2B27; historical attribution:
Physlib/QuantumMechanics/Operators/Unbounded.lean, Adam Bornemann
and Gregory J. Loges (2026), leanprover-community/physlib
@e411c6e89692e83bc67fe451302ae7f82cf39b10, Apache-2.0.
No Physlib import or source/model proxy.

This does not identify the independent manuscript abstract
Cl(48)/Spin(48) gauge model with the source Fock representation;
does not prove global Spin(9) high-weight bounds, positive point
spectrum, a ground-state count or BFSS mass gap.
-/

set_option autoImplicit false
set_option maxHeartbeats 250000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8BE
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open FCP.BFSSSU2PhysicalDomainL6H5E8BA
open FCP.BFSSSU2PhysicalDomainL6H5E8BB
open FCP.BFSSSU2PhysicalDomainL6H5E8BC
open FCP.BFSSSU2PhysicalDomainL6H5E8BD
open LinearPMap
open scoped ComplexConjugate

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



/-- Exact adjoint of nonzero-scaled densely defined partial operator,
proved in our frozen Mathlib without an external dependency. -/
theorem adjoint_smul_of_dense (U : E →ₗ.[ℂ] F)
    (hd : Dense (U.domain : Set E)) {c : ℂ} (hc : c ≠ 0) :
    (c • U).adjoint = (starRingEnd ℂ) c • U.adjoint := by
  refine LinearPMap.dExt ?_ fun x y hxy => ?_
  · ext x
    change Continuous (fun w => inner ℂ x (c • U w)) ↔
      Continuous (fun w => inner ℂ x (U w))
    exact Iff.trans (by simp [inner_smul_right])
      (continuous_const_smul_iff₀ hc)
  · refine LinearPMap.adjoint_apply_eq
      (by simpa only [LinearPMap.smul_domain] using hd) x fun w => ?_
    simp [inner_smul_left, inner_smul_right,
      LinearPMap.adjoint_isFormalAdjoint hd y w, hxy]

/-- Scalar multiplication by any nonzero REAL complex scalar
preserves genuine self-adjointness, including the domain equality. -/
theorem selfAdjoint_smul_real (A : E →ₗ.[ℂ] E)
    (hA : IsSelfAdjoint A) {c : ℂ}
    (hc : c ≠ 0) (hr : (starRingEnd ℂ) c = c) :
    IsSelfAdjoint (c • A) := by
  change (c • A).adjoint = c • A
  rw [adjoint_smul_of_dense A hA.dense_domain hc,
    hr, LinearPMap.isSelfAdjoint_def.mp hA]



variable (M : AlgebraData 2) (G : M.GaugeData)

/-- The ACTUAL pinned N=2 source physical charge closed form's
representing-vector condition is equivalent to the natural domain
of its actual Hilbert adjoint-square, with the exact coefficient. -/
theorem originalMinimalPhysicalNormalizedWeakForm_associatedOperator_iff
    (u : (originalMinimalPhysicalHilbertChargeColumn M G).domain)
    (w : G.physicalSpace) :
    (∀ v : (originalMinimalPhysicalHilbertChargeColumn M G).domain,
      inner ℂ w (v : G.physicalSpace) =
        (1 / 16 : ℂ) *
          inner ℂ (originalMinimalPhysicalHilbertChargeColumn M G u)
            (originalMinimalPhysicalHilbertChargeColumn M G v)) ↔
      ∃ h : (u : G.physicalSpace) ∈
          (originalMinimalPhysicalHilbertChargeAdjointSquare M G).domain,
        w = (1 / 16 : ℂ) •
          (originalMinimalPhysicalHilbertChargeAdjointSquare M G ⟨u, h⟩) := by
  letI : CompleteSpace G.physicalSpace :=
    originalPhysicalHilbertComplete M G
  exact normalizedWeakRepresentative_iff_naturalAdjointSquare
    (originalMinimalPhysicalHilbertChargeColumn M G)
    (originalMinimalPhysicalHilbertChargeColumn_domain_dense_unconditional M G) u w



/-- The actual NORMALIZED physical source BFSS Hamiltonian,
on exactly the natural domain of T†T, no artificial extension. -/
noncomputable def originalMinimalPhysicalNormalizedHamiltonian :
    G.physicalSpace →ₗ.[ℂ] G.physicalSpace :=
  (1 / 16 : ℂ) • originalMinimalPhysicalHilbertChargeAdjointSquare M G

/-- The scalar normalization changes NONE of the source-domain points. -/
theorem originalMinimalPhysicalNormalizedHamiltonian_domain :
    (originalMinimalPhysicalNormalizedHamiltonian M G).domain =
      (originalMinimalPhysicalHilbertChargeAdjointSquare M G).domain := by
  rfl

/-- The actual Hamiltonian action on the original natural domain. -/
theorem originalMinimalPhysicalNormalizedHamiltonian_apply
    (u : (originalMinimalPhysicalHilbertChargeAdjointSquare M G).domain) :
    originalMinimalPhysicalNormalizedHamiltonian M G
      ⟨u, by rw [originalMinimalPhysicalNormalizedHamiltonian_domain M G]; exact u.property⟩ =
        (1 / 16 : ℂ) • originalMinimalPhysicalHilbertChargeAdjointSquare M G u := by
  rfl

/-- GENUINE self-adjointness of the normalized original source
physical Hamiltonian—not just formal symmetry. -/
theorem originalMinimalPhysicalNormalizedHamiltonian_selfAdjoint :
    letI : CompleteSpace G.physicalSpace :=
      originalPhysicalHilbertComplete M G
    IsSelfAdjoint (originalMinimalPhysicalNormalizedHamiltonian M G) := by
  letI : CompleteSpace G.physicalSpace :=
    originalPhysicalHilbertComplete M G
  apply selfAdjoint_smul_real (originalMinimalPhysicalHilbertChargeAdjointSquare M G)
    (originalMinimalPhysicalHilbertChargeAdjointSquare_selfAdjoint M G)
    (by norm_num)
  simp only [map_div₀, map_one, map_ofNat]

/-- The weak-form representing-vector equation selects exactly
this very normalized source Hamiltonian, including its domain. -/
theorem originalMinimalPhysicalNormalizedHamiltonian_weakForm_iff
    (u : (originalMinimalPhysicalHilbertChargeColumn M G).domain)
    (w : G.physicalSpace) :
    (∀ v : (originalMinimalPhysicalHilbertChargeColumn M G).domain,
      inner ℂ w (v : G.physicalSpace) =
        (1 / 16 : ℂ) *
          inner ℂ (originalMinimalPhysicalHilbertChargeColumn M G u)
            (originalMinimalPhysicalHilbertChargeColumn M G v)) ↔
      ∃ h : (u : G.physicalSpace) ∈
          (originalMinimalPhysicalNormalizedHamiltonian M G).domain,
        w = originalMinimalPhysicalNormalizedHamiltonian M G ⟨u, h⟩ := by
  exact originalMinimalPhysicalNormalizedWeakForm_associatedOperator_iff M G u w

theorem originalMinimalPhysicalNormalizedHamiltonian_closed :
    (originalMinimalPhysicalNormalizedHamiltonian M G).IsClosed := by
  letI : CompleteSpace G.physicalSpace :=
    originalPhysicalHilbertComplete M G
  exact (originalMinimalPhysicalNormalizedHamiltonian_selfAdjoint M G).isClosed

theorem originalMinimalPhysicalNormalizedHamiltonian_domain_dense :
    Dense ((originalMinimalPhysicalNormalizedHamiltonian M G).domain :
      Set G.physicalSpace) := by
  letI : CompleteSpace G.physicalSpace :=
    originalPhysicalHilbertComplete M G
  exact (originalMinimalPhysicalNormalizedHamiltonian_selfAdjoint M G).dense_domain



#print axioms weakRepresentative_iff_adjoint
#print axioms weakRepresentative_iff_naturalAdjointSquare
#print axioms sixteen_inner_smul
#print axioms one_sixteenth_inner_smul
#print axioms normalizedWeakRepresentative_iff_naturalAdjointSquare
#print axioms adjoint_smul_of_dense
#print axioms selfAdjoint_smul_real
#print axioms originalMinimalPhysicalNormalizedWeakForm_associatedOperator_iff
#print axioms originalMinimalPhysicalNormalizedHamiltonian_domain
#print axioms originalMinimalPhysicalNormalizedHamiltonian_apply
#print axioms originalMinimalPhysicalNormalizedHamiltonian_selfAdjoint
#print axioms originalMinimalPhysicalNormalizedHamiltonian_weakForm_iff
#print axioms originalMinimalPhysicalNormalizedHamiltonian_closed
#print axioms originalMinimalPhysicalNormalizedHamiltonian_domain_dense

end
end FCP.BFSSSU2PhysicalDomainL6H5E8BE
