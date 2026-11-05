import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Algebra.Hom

/-!
Independent M3J algebraic existence lemma, exact target Mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612 / Lean 4.34.1.

E is an independent module, not a space transported from V. The only
representation input is a unital algebra hom from the FULL endomorphism
algebra of the finite-dimensional source. No intertwiner is assumed.

The column construction is the matrix-unit argument in rank-one form.
It does not assert a Hilbert isometry or Clifford adjoint compatibility.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.IndependentM3J
noncomputable section

variable {K V E I : Type*} [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup E] [Module K E]

/-- Rank-one column evaluated in an independent full-endomorphism module. -/
def columnIntertwiner
    (rho : Module.End K V →ₐ[K] Module.End K E)
    (f : V →ₗ[K] K) (w : E) : V →ₗ[K] E :=
  (LinearMap.applyₗ w).comp
    (rho.toLinearMap.comp (LinearMap.smulRightₗ f))

theorem columnIntertwiner_intertwines
    (rho : Module.End K V →ₐ[K] Module.End K E)
    (f : V →ₗ[K] K) (w : E) (a : Module.End K V) (x : V) :
    columnIntertwiner rho f w (a x) =
      rho a (columnIntertwiner rho f w x) := by
  have h : f.smulRight (a x) = a * f.smulRight x := by
    ext y
    exact (a.map_smul (f y) x).symm
  change rho (f.smulRight (a x)) w = rho a (rho (f.smulRight x) w)
  rw [h, map_mul, Module.End.mul_apply]

/-- Unitality and a finite source basis CONSTRUCT a nonzero intertwiner.
No target irreducibility, dimension or inner product is required. -/
theorem exists_nonzero_fullEnd_intertwiner [Fintype I] [Nontrivial E]
    (b : Module.Basis I K V)
    (rho : Module.End K V →ₐ[K] Module.End K E) :
    ∃ (T : V →ₗ[K] E) (x : V), T x ≠ 0 ∧
      ∀ (a : Module.End K V) (v : V), T (a v) = rho a (T v) := by
  classical
  have hid : (∑ i, (b.coord i).smulRight (b i)) =
      (1 : Module.End K V) := by
    ext v
    simpa only [LinearMap.sum_apply, LinearMap.smulRight_apply,
      Module.Basis.coord_apply, Module.End.one_apply] using b.sum_repr v
  obtain ⟨w, hw⟩ := exists_ne (0 : E)
  have hsum : (∑ i, rho ((b.coord i).smulRight (b i)) w) = w := by
    rw [← LinearMap.sum_apply, ← map_sum, hid, map_one, Module.End.one_apply]
  have hsome : ∃ i, rho ((b.coord i).smulRight (b i)) w ≠ 0 := by
    by_contra hn
    have hz : ∀ i, rho ((b.coord i).smulRight (b i)) w = 0 := by
      simpa only [not_exists, not_not] using hn
    apply hw
    rw [← hsum]
    exact Finset.sum_eq_zero fun i _ => hz i
  obtain ⟨i, hi⟩ := hsome
  refine ⟨columnIntertwiner rho (b.coord i) w, b i, hi, ?_⟩
  exact columnIntertwiner_intertwines rho (b.coord i) w

/-- Every nonzero intertwiner from the defining full-endomorphism
module is injective. This proves source simplicity directly from
rank-one maps and does not impose it on an independent target. -/
theorem nonzero_fullEnd_intertwiner_injective
    (b : Module.Basis I K V)
    (rho : Module.End K V →ₐ[K] Module.End K E)
    (T : V →ₗ[K] E) (x0 : V) (hx0 : T x0 ≠ 0)
    (hT : ∀ (a : Module.End K V) (v : V), T (a v) = rho a (T v)) :
    Function.Injective T := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  by_contra hnx
  have hsome : ∃ i, b.coord i x ≠ 0 := by
    by_contra hn
    apply hnx
    apply b.forall_coord_eq_zero_iff.mp
    simpa only [not_exists, not_not] using hn
  obtain ⟨i, hi⟩ := hsome
  have hz : (b.coord i x) • T x0 = 0 := by
    calc
      (b.coord i x) • T x0 = T (((b.coord i).smulRight x0) x) :=
        (T.map_smul (b.coord i x) x0).symm
      _ = rho ((b.coord i).smulRight x0) (T x) := hT _ x
      _ = 0 := by rw [hx, map_zero]
  exact hx0 ((smul_eq_zero.mp hz).resolve_left hi)

/-- The missing algebraic equivalence is obtained by construction.
The target is arbitrary and nonzero; irreducibility is its only extra
hypothesis. No target finrank equality or intertwiner is assumed. -/
theorem exists_fullEnd_intertwining_equiv [Fintype I] [Nontrivial E]
    (b : Module.Basis I K V)
    (rho : Module.End K V →ₐ[K] Module.End K E)
    (hirr : ∀ W : Submodule K E,
      (∀ a : Module.End K V, ∀ w ∈ W, rho a w ∈ W) →
        W = ⊥ ∨ W = ⊤) :
    ∃ T : V ≃ₗ[K] E,
      ∀ (a : Module.End K V) (v : V), T (a v) = rho a (T v) := by
  obtain ⟨T, x0, hx0, hT⟩ := exists_nonzero_fullEnd_intertwiner b rho
  have hinj := nonzero_fullEnd_intertwiner_injective b rho T x0 hx0 hT
  have hrange : T.range = ⊤ := by
    have hstable : ∀ a : Module.End K V, ∀ w ∈ T.range, rho a w ∈ T.range := by
      intro a w hw
      obtain ⟨v, rfl⟩ := hw
      exact ⟨a v, hT a v⟩
    rcases hirr T.range hstable with hbot | htop
    · have hx : T x0 ∈ T.range := ⟨x0, rfl⟩
      rw [hbot] at hx
      exact (hx0 ((Submodule.mem_bot K).mp hx)).elim
    · exact htop
  refine ⟨LinearEquiv.ofBijective T
    ⟨hinj, LinearMap.range_eq_top.mp hrange⟩, ?_⟩
  exact hT

/-- An algebra equivalence with the full source endomorphism algebra
gives equivalence of every independent nonzero irreducible unital
module. The representation is an input; its intertwiner is an output. -/
theorem exists_algebra_intertwining_equiv
    {A : Type*} [Ring A] [Algebra K A]
    [Fintype I] [Nontrivial E]
    (b : Module.Basis I K V)
    (Phi : A ≃ₐ[K] Module.End K V)
    (sigma : A →ₐ[K] Module.End K E)
    (hirr : ∀ W : Submodule K E,
      (∀ a : A, ∀ w ∈ W, sigma a w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ T : V ≃ₗ[K] E,
      ∀ (a : A) (v : V), T (Phi a v) = sigma a (T v) := by
  let rho := sigma.comp Phi.symm.toAlgHom
  have hr : ∀ W : Submodule K E,
      (∀ a : Module.End K V, ∀ w ∈ W, rho a w ∈ W) →
        W = ⊥ ∨ W = ⊤ := by
    intro W hW
    apply hirr W
    intro a w hw
    have h := hW (Phi a) w hw
    simpa only [rho, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.symm_apply_apply] using h
  obtain ⟨T, hT⟩ := exists_fullEnd_intertwining_equiv b rho hr
  refine ⟨T, ?_⟩
  intro a v
  simpa only [rho, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply] using hT (Phi a) v

#print axioms columnIntertwiner
#print axioms columnIntertwiner_intertwines
#print axioms exists_nonzero_fullEnd_intertwiner
#print axioms nonzero_fullEnd_intertwiner_injective
#print axioms exists_fullEnd_intertwining_equiv
#print axioms exists_algebra_intertwining_equiv

end
end FCP.IndependentM3J
