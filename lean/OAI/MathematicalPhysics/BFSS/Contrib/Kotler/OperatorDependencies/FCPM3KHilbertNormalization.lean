import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Positive scalar normalization of a generator-intertwining equivalence.
Only genuine Hilbert adjoints occur here. No Clifford Star instance
is used. The source scalar-commutant hypothesis is intended to be
discharged by the already accepted original pairedTheta theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.IndependentM3K
noncomputable section

variable {V E L : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ E] [Nontrivial V]

/-- Normalize an invertible intertwiner by a POSITIVE real square root.
The source commutant, not a new Schur theorem on E, suffices. -/
theorem positive_normalization_of_intertwining_equiv
    (source : L → Module.End ℂ V) (target : L → Module.End ℂ E)
    (hsource : ∀ l, (source l).IsSymmetric)
    (htarget : ∀ l, (target l).IsSymmetric)
    (hscalar : ∀ G : Module.End ℂ V,
      (∀ l v, G (source l v) = source l (G v)) →
        ∃ c : ℂ, G = c • (1 : Module.End ℂ V))
    (T : V ≃ₗ[ℂ] E)
    (hT : ∀ l v, T (source l v) = target l (T v)) :
    ∃ (U : V ≃ₗᵢ[ℂ] E) (r : ℝ), 0 < r ∧
      (∀ v, U v = (r : ℂ)⁻¹ • T v) ∧
      (∀ l v, U (source l v) = target l (U v)) := by
  let S := T.toLinearMap
  have hadj : ∀ l, (source l).comp S.adjoint = S.adjoint.comp (target l) := by
    intro l
    have h : S.comp (source l) = (target l).comp S := by
      ext v
      exact hT l v
    have hh := congrArg LinearMap.adjoint h
    simpa only [LinearMap.adjoint_comp,
      (hsource l).adjoint_eq, (htarget l).adjoint_eq] using hh
  let G : Module.End ℂ V := S.adjoint.comp S
  have hG : ∀ l v, G (source l v) = source l (G v) := by
    intro l v
    change S.adjoint (T (source l v)) = source l (S.adjoint (T v))
    rw [hT]
    exact (LinearMap.congr_fun (hadj l) (T v)).symm
  obtain ⟨c, hc⟩ := hscalar G hG
  have hnormsq : ∀ v : V, ‖T v‖ ^ 2 = c.re * ‖v‖ ^ 2 := by
    intro v
    have h : inner ℂ v (G v) = inner ℂ (T v) (T v) :=
      S.adjoint_inner_right v (S v)
    rw [hc] at h
    simp only [LinearMap.smul_apply, Module.End.one_apply,
      inner_smul_right, inner_self_eq_norm_sq_to_K] at h
    have hh := congrArg (RCLike.re : ℂ → ℝ) h
    simpa only [RCLike.mul_re, RCLike.re_ofReal_pow,
      RCLike.im_ofReal_pow, mul_zero, sub_zero,
      RCLike.re_eq_complex_re] using hh.symm
  obtain ⟨v0, hv0⟩ := exists_ne (0 : V)
  have hTv0 : T v0 ≠ 0 := by
    intro h
    apply hv0
    exact T.injective (h.trans T.map_zero.symm)
  have hcpos : 0 < c.re := by
    apply pos_of_mul_pos_left (b := ‖v0‖ ^ 2) _ (sq_nonneg _)
    rw [← hnormsq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hTv0)
  let r := Real.sqrt c.re
  have hr : 0 < r := Real.sqrt_pos.mpr hcpos
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hnorm : ∀ v : V, ‖T v‖ = r * ‖v‖ := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hr.le (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hcpos.le]
    exact hnormsq v
  let U0 : V →ₗᵢ[ℂ] E :=
    { toLinearMap := (r : ℂ)⁻¹ • S
      norm_map' := by
        intro v
        change ‖(r : ℂ)⁻¹ • T v‖ = ‖v‖
        rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr, hnorm, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul] }
  have hsurj : Function.Surjective U0 := by
    intro w
    refine ⟨T.symm ((r : ℂ) • w), ?_⟩
    change (r : ℂ)⁻¹ • T (T.symm ((r : ℂ) • w)) = w
    rw [T.apply_symm_apply, smul_smul, inv_mul_cancel₀ hrc, one_smul]
  let U := LinearIsometryEquiv.ofSurjective U0 hsurj
  refine ⟨U, r, hr, (fun _ => rfl), ?_⟩
  intro l v
  change (r : ℂ)⁻¹ • T (source l v) = target l ((r : ℂ)⁻¹ • T v)
  rw [hT, map_smul]

#print axioms positive_normalization_of_intertwining_equiv

end
end FCP.IndependentM3K
