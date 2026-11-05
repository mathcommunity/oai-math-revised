import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G1OriginalUpstreamSpinIdentityProbe

/-!
# L6-G2 — arbitrary real spinors and the original row-spinor Fierz sign

Candidate until independently compiled and axiom-audited under the pinned
environment. Reuses L6-G1; does not rebuild the Clifford-word basis.
Only the unchanged original real gamma construction occurs here.
This is a finite matrix identity, not a CAR/Gauss operator or domain theorem.
-/
namespace FCP.BFSSSU2PhysicalDomainL6G2
noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators
open OAI.BFSSGamma
open FCP.BFSSSU2PhysicalDomainL6G1

def spinorSquareNorm (w : Spin → ℝ) : ℝ := ∑ α, w α ^ 2

private theorem matrix_mulVec_smul (A : Mat) (c : ℝ) (v : Spin → ℝ) :
    A *ᵥ (c • v) = c • (A *ᵥ v) := by
  ext r
  change (∑ s, A r s * (c * v s)) = c * (∑ s, A r s * v s)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem symm_outer_smul (c : ℝ) (a b : Spin → ℝ) :
    symm (Matrix.vecMulVec (c • a) (c • b)) =
      c ^ 2 • symm (Matrix.vecMulVec a b) := by
  ext r s
  change (1 / 2 : ℝ) * ((c * a r) * (c * b s) + (c * a s) * (c * b r)) =
    c ^ 2 * ((1 / 2 : ℝ) * (a r * b s + a s * b r))
  ring

private theorem spinLHS_smul (G : Space → Mat) (c : ℝ)
    (v : Spin → ℝ) (j : Space) :
    spinLHS G (c • v) j = c ^ 2 • spinLHS G v j := by
  unfold spinLHS
  simp_rw [matrix_mulVec_smul, symm_outer_smul]
  rw [Finset.smul_sum]

private theorem dot_mulVec_smul (A : Mat) (c : ℝ) (v : Spin → ℝ) :
    dotProduct (c • v) (A *ᵥ (c • v)) =
      c ^ 2 * dotProduct v (A *ᵥ v) := by
  rw [matrix_mulVec_smul]
  change (∑ α, (c * v α) * (c * (A *ᵥ v) α)) =
    c ^ 2 * (∑ α, v α * (A *ᵥ v) α)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  ring

/-- The original upstream column-spinor identity, extended by quadratic
homogeneity to every real spinor, including the zero spinor. -/
theorem originalGamma_spinIdentity_homogeneous
    (w : Spin → ℝ) (j : Space) :
    spinLHS originalGamma w j =
      ((1 / 2 : ℝ) * dotProduct w (originalGamma j *ᵥ w)) • (1 : Mat) -
        ((1 / 2 : ℝ) * spinorSquareNorm w) • originalGamma j := by
  let q : ℝ := spinorSquareNorm w
  have hq : 0 ≤ q := Finset.sum_nonneg (fun α _ => sq_nonneg (w α))
  by_cases hzero : q = 0
  · have hw : w = 0 := by
      ext α
      have hle : w α ^ 2 ≤ q :=
        Finset.single_le_sum (fun β _ => sq_nonneg (w β)) (Finset.mem_univ α)
      change w α = 0
      nlinarith
    rw [hw]
    simp [spinLHS, OAI.BFSSGamma.symm, spinorSquareNorm]
  · let t : ℝ := Real.sqrt q
    have hsq : t ^ 2 = q := Real.sq_sqrt hq
    have ht : t ≠ 0 := by
      intro h
      apply hzero
      rw [← hsq, h]
      norm_num
    let v : Spin → ℝ := fun α => w α / t
    have hv : ∑ α, v α ^ 2 = 1 := by
      simp only [v, div_pow]
      rw [← Finset.sum_div]
      change q / t ^ 2 = 1
      rw [hsq]
      exact div_self hzero
    have hwv : w = t • v := by
      ext α
      change w α = t * (w α / t)
      field_simp [ht] <;> ring
    have hd : dotProduct w (originalGamma j *ᵥ w) =
        t ^ 2 * dotProduct v (originalGamma j *ᵥ v) := by
      rw [hwv, dot_mulVec_smul]
    have hI : t ^ 2 * ((1 / 2 : ℝ) * dotProduct v (originalGamma j *ᵥ v)) =
        (1 / 2 : ℝ) * dotProduct w (originalGamma j *ᵥ w) := by
      rw [hd]
      ring
    have hG : t ^ 2 * (1 / 2 : ℝ) = (1 / 2 : ℝ) * spinorSquareNorm w := by
      change t ^ 2 * (1 / 2 : ℝ) = (1 / 2 : ℝ) * q
      rw [hsq]
      ring
    calc
      _ = t ^ 2 • spinLHS originalGamma v j := by rw [hwv, spinLHS_smul]
      _ = t ^ 2 •
          (((1 / 2 : ℝ) * dotProduct v (originalGamma j *ᵥ v)) • (1 : Mat) -
            (1 / 2 : ℝ) • originalGamma j) :=
        congrArg (fun A : Mat => t ^ 2 • A) (originalGamma_spinIdentity_apply v hv j)
      _ = _ := by rw [smul_sub, smul_smul, smul_smul, hI, hG]

/-- The sign that distinguishes row and column gammaTwo contractions. -/
theorem originalGammaTwo_transpose (i j : Space) :
    (gammaTwo originalGamma i j).transpose = -gammaTwo originalGamma i j := by
  have hi : (originalGamma i).transpose = originalGamma i :=
    FCP.BFSSGamma9.gamma_symmetric i
  have hj : (originalGamma j).transpose = originalGamma j :=
    FCP.BFSSGamma9.gamma_symmetric j
  simp only [gammaTwo, Matrix.transpose_smul, Matrix.transpose_sub,
    Matrix.transpose_mul, hi, hj, ← smul_neg, neg_sub]

private theorem row_eq_transpose_mulVec (A : Mat) (w : Spin → ℝ) :
    w ᵥ* A = A.transpose *ᵥ w := by
  ext r
  change (∑ s, w s * A s r) = ∑ s, A s r * w s
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem originalGamma_row_eq_column (w : Spin → ℝ) (i : Space) :
    w ᵥ* originalGamma i = originalGamma i *ᵥ w := by
  have hi : (originalGamma i).transpose = originalGamma i :=
    FCP.BFSSGamma9.gamma_symmetric i
  rw [row_eq_transpose_mulVec, hi]

theorem originalGammaTwo_row_eq_neg_column
    (w : Spin → ℝ) (i j : Space) :
    w ᵥ* gammaTwo originalGamma i j = -(gammaTwo originalGamma i j *ᵥ w) := by
  rw [row_eq_transpose_mulVec, originalGammaTwo_transpose, Matrix.neg_mulVec]

/-- Literal real row-spinor Fierz entries for the unchanged original gamma
construction. No unit-length hypothesis and no operator-domain conclusion. -/
theorem originalGamma_generalizedRowFierz
    (w : Spin → ℝ) (p : Space) (r s : Spin) :
    (∑ i : Space,
      ((w ᵥ* originalGamma i) r * (w ᵥ* gammaTwo originalGamma i p) s +
       (w ᵥ* originalGamma i) s * (w ᵥ* gammaTwo originalGamma i p) r)) =
      spinorSquareNorm w * originalGamma p r s -
        (if r = s then dotProduct w (originalGamma p *ᵥ w) else 0) := by
  have h := congrArg (fun A : Mat => A r s)
    (originalGamma_spinIdentity_homogeneous w p)
  have hentry :
      (∑ i : Space, (1 / 2 : ℝ) *
        ((originalGamma i *ᵥ w) r * (gammaTwo originalGamma i p *ᵥ w) s +
         (originalGamma i *ᵥ w) s * (gammaTwo originalGamma i p *ᵥ w) r)) =
      ((1 / 2 : ℝ) * dotProduct w (originalGamma p *ᵥ w)) *
        (if r = s then 1 else 0) -
      ((1 / 2 : ℝ) * spinorSquareNorm w) * originalGamma p r s := by
    simpa only [spinLHS, OAI.BFSSGamma.symm, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply,
      Matrix.vecMulVec_apply, Matrix.one_apply, smul_eq_mul] using h
  have hleft :
      (∑ i : Space,
        ((w ᵥ* originalGamma i) r * (w ᵥ* gammaTwo originalGamma i p) s +
         (w ᵥ* originalGamma i) s * (w ᵥ* gammaTwo originalGamma i p) r)) =
      -2 * (∑ i : Space, (1 / 2 : ℝ) *
        ((originalGamma i *ᵥ w) r * (gammaTwo originalGamma i p *ᵥ w) s +
         (originalGamma i *ᵥ w) s * (gammaTwo originalGamma i p *ᵥ w) r)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [originalGamma_row_eq_column, originalGammaTwo_row_eq_neg_column,
      Pi.neg_apply]
    ring
  rw [hleft]
  by_cases hrs : r = s
  · simp only [hrs, ite_true] at hentry ⊢
    nlinarith [hentry]
  · simp only [hrs, ite_false] at hentry ⊢
    nlinarith [hentry]

#print axioms originalGamma_spinIdentity_homogeneous
#print axioms originalGammaTwo_transpose
#print axioms originalGamma_row_eq_column
#print axioms originalGammaTwo_row_eq_neg_column
#print axioms originalGamma_generalizedRowFierz
#check @originalGamma_generalizedRowFierz

end
end FCP.BFSSSU2PhysicalDomainL6G2
