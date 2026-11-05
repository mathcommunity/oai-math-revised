import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CKOrthogonalCompletionCoordinates
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! F10CL: smoothness and the strict identity derivative of the accepted completion map.
Use scalar entry products and finite sums on the existing matrix product topology.
Local matrix injectivity, source fibers and source coverage remain separate obligations.
Candidate until complete strict source compilation and independent audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

/-- The actual original row/column evaluation as a continuous linear map. -/
noncomputable def source9CompletionEntryCLM (i j : SpaceIndex) :
    Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (SpaceIndex → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i :
      (SpaceIndex → SpaceIndex → ℝ) →L[ℝ] (SpaceIndex → ℝ))

theorem source9CompletionEntryCLM_apply (i j : SpaceIndex) (B : Matrix SpaceIndex SpaceIndex ℝ) :
    source9CompletionEntryCLM i j B = B i j := rfl

private theorem completionGramEntry_eq_sum (i j : SpaceIndex) :
    (fun B : Matrix SpaceIndex SpaceIndex ℝ => (B.transpose * B) i j) =
      (fun B : Matrix SpaceIndex SpaceIndex ℝ => ∑ k : SpaceIndex, B k i * B k j) := rfl

theorem source9CompletionGramEntry_contDiff (n : ℕ∞ω) (i j : SpaceIndex) :
    ContDiff ℝ n (fun B : Matrix SpaceIndex SpaceIndex ℝ => (B.transpose * B) i j) := by
  rw [completionGramEntry_eq_sum i j]
  apply ContDiff.sum
  intro k _
  exact (source9CompletionEntryCLM k i).contDiff.mul (source9CompletionEntryCLM k j).contDiff

/-- Each quadratic Gram entry has the literal zero continuous linear derivative at zero. -/
theorem source9CompletionGramEntry_hasFDerivAt_zero (i j : SpaceIndex) :
    HasFDerivAt (fun B : Matrix SpaceIndex SpaceIndex ℝ => (B.transpose * B) i j)
      (0 : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ) 0 := by
  have hprod (k : SpaceIndex) :
      HasFDerivAt (fun B : Matrix SpaceIndex SpaceIndex ℝ => B k i * B k j)
        (0 : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ) 0 := by
    have hki : HasFDerivAt (fun B : Matrix SpaceIndex SpaceIndex ℝ => B k i)
        (source9CompletionEntryCLM k i) (0 : Matrix SpaceIndex SpaceIndex ℝ) :=
      (source9CompletionEntryCLM k i).hasFDerivAt
    have hkj : HasFDerivAt (fun B : Matrix SpaceIndex SpaceIndex ℝ => B k j)
        (source9CompletionEntryCLM k j) (0 : Matrix SpaceIndex SpaceIndex ℝ) :=
      (source9CompletionEntryCLM k j).hasFDerivAt
    have h := hki.mul hkj
    change HasFDerivAt (fun B : Matrix SpaceIndex SpaceIndex ℝ => B k i * B k j)
      ((0 : ℝ) • source9CompletionEntryCLM k j + (0 : ℝ) • source9CompletionEntryCLM k i)
      (0 : Matrix SpaceIndex SpaceIndex ℝ) at h
    simpa only [zero_smul, add_zero] using h
  have hsum : HasFDerivAt
      (fun B : Matrix SpaceIndex SpaceIndex ℝ => ∑ k : SpaceIndex, B k i * B k j)
      (∑ _k : SpaceIndex, (0 : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ))
      (0 : Matrix SpaceIndex SpaceIndex ℝ) :=
    HasFDerivAt.fun_sum (u := Finset.univ)
      (A := fun k : SpaceIndex => fun B : Matrix SpaceIndex SpaceIndex ℝ => B k i * B k j)
      (A' := fun _ : SpaceIndex => (0 : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ))
      (fun k _ => hprod k)
  have hzero : (∑ _k : SpaceIndex, (0 : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ)) = 0 :=
    Finset.sum_const_zero
  have hs : HasFDerivAt
      (fun B : Matrix SpaceIndex SpaceIndex ℝ => ∑ k : SpaceIndex, B k i * B k j)
      (0 : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ) (0 : Matrix SpaceIndex SpaceIndex ℝ) :=
    Eq.mp (congrArg (fun L : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ =>
      HasFDerivAt (fun B : Matrix SpaceIndex SpaceIndex ℝ => ∑ k : SpaceIndex, B k i * B k j)
        L (0 : Matrix SpaceIndex SpaceIndex ℝ)) hzero) hsum
  rw [← completionGramEntry_eq_sum i j] at hs
  exact hs

theorem source9OrthogonalCompletionMap_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n source9OrthogonalCompletionMap := by
  apply contDiff_pi.2
  intro i
  apply contDiff_pi.2
  intro j
  have he : ContDiff ℝ n (fun B : Matrix SpaceIndex SpaceIndex ℝ => B i j) :=
    (source9CompletionEntryCLM i j).contDiff
  have hq := source9CompletionGramEntry_contDiff n i j
  by_cases hij : i < j
  · simpa only [source9OrthogonalCompletionMap, ite_eq_left hij] using he
  · by_cases hji : j < i
    · simpa only [source9OrthogonalCompletionMap, ite_eq_right hij, ite_eq_left hji] using he.add hq
    · simpa only [source9OrthogonalCompletionMap, ite_eq_right hij, ite_eq_right hji] using
        he.add (hq.div_const 2)

/-- Complete operator equality: the derivative acts identically on every original matrix entry. -/
theorem source9OrthogonalCompletionMap_hasFDerivAt_zero :
    HasFDerivAt source9OrthogonalCompletionMap
      (ContinuousLinearMap.id ℝ (Matrix SpaceIndex SpaceIndex ℝ)) 0 := by
  have hadd {f g : Matrix SpaceIndex SpaceIndex ℝ → ℝ}
      {L : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ}
      (hf : HasFDerivAt f L (0 : Matrix SpaceIndex SpaceIndex ℝ))
      (hg : HasFDerivAt g (0 : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ)
        (0 : Matrix SpaceIndex SpaceIndex ℝ)) :
      HasFDerivAt (fun B : Matrix SpaceIndex SpaceIndex ℝ => f B + g B)
        L (0 : Matrix SpaceIndex SpaceIndex ℝ) := by
    have hsum : HasFDerivAt (fun B : Matrix SpaceIndex SpaceIndex ℝ => f B + g B)
        (L + (0 : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ))
        (0 : Matrix SpaceIndex SpaceIndex ℝ) := hf.add hg
    have hzero : L + (0 : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ) = L := add_zero L
    exact Eq.mp (congrArg (fun M : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ =>
      HasFDerivAt (fun B : Matrix SpaceIndex SpaceIndex ℝ => f B + g B)
        M (0 : Matrix SpaceIndex SpaceIndex ℝ)) hzero) hsum
  have hentry (i j : SpaceIndex) : HasFDerivAt
      (fun B : Matrix SpaceIndex SpaceIndex ℝ => source9OrthogonalCompletionMap B i j)
      (source9CompletionEntryCLM i j) (0 : Matrix SpaceIndex SpaceIndex ℝ) := by
    have he : HasFDerivAt (fun B : Matrix SpaceIndex SpaceIndex ℝ => B i j)
        (source9CompletionEntryCLM i j) (0 : Matrix SpaceIndex SpaceIndex ℝ) :=
      (source9CompletionEntryCLM i j).hasFDerivAt
    have hq := source9CompletionGramEntry_hasFDerivAt_zero i j
    by_cases hij : i < j
    · simpa only [source9OrthogonalCompletionMap, ite_eq_left hij] using he
    · by_cases hji : j < i
      · have hsum : HasFDerivAt
            (fun B : Matrix SpaceIndex SpaceIndex ℝ => B i j + (B.transpose * B) i j)
            (source9CompletionEntryCLM i j) (0 : Matrix SpaceIndex SpaceIndex ℝ) := hadd he hq
        have hfun :
            (fun B : Matrix SpaceIndex SpaceIndex ℝ => source9OrthogonalCompletionMap B i j) =
            (fun B : Matrix SpaceIndex SpaceIndex ℝ => B i j + (B.transpose * B) i j) := by
          funext B
          simp only [source9OrthogonalCompletionMap, ite_eq_right hij, ite_eq_left hji]
        exact Eq.mp (congrArg (fun f : Matrix SpaceIndex SpaceIndex ℝ → ℝ =>
          HasFDerivAt f (source9CompletionEntryCLM i j) (0 : Matrix SpaceIndex SpaceIndex ℝ))
          hfun.symm) hsum
      · have hhalf : HasFDerivAt
            (fun B : Matrix SpaceIndex SpaceIndex ℝ => (B.transpose * B) i j / 2)
            (0 : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ) 0 := by
          have hmul : HasFDerivAt
              (fun B : Matrix SpaceIndex SpaceIndex ℝ => (B.transpose * B) i j * (2 : ℝ)⁻¹)
              ((2 : ℝ)⁻¹ • (0 : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ))
              (0 : Matrix SpaceIndex SpaceIndex ℝ) := hq.mul_const ((2 : ℝ)⁻¹)
          have hzero : (2 : ℝ)⁻¹ • (0 : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ) = 0 :=
            smul_zero ((2 : ℝ)⁻¹)
          have hmulzero : HasFDerivAt
              (fun B : Matrix SpaceIndex SpaceIndex ℝ => (B.transpose * B) i j * (2 : ℝ)⁻¹)
              (0 : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ) (0 : Matrix SpaceIndex SpaceIndex ℝ) :=
            Eq.mp (congrArg (fun M : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ =>
              HasFDerivAt
                (fun B : Matrix SpaceIndex SpaceIndex ℝ => (B.transpose * B) i j * (2 : ℝ)⁻¹)
                M (0 : Matrix SpaceIndex SpaceIndex ℝ)) hzero) hmul
          have hdiv :
              (fun B : Matrix SpaceIndex SpaceIndex ℝ => (B.transpose * B) i j / 2) =
              (fun B : Matrix SpaceIndex SpaceIndex ℝ => (B.transpose * B) i j * (2 : ℝ)⁻¹) := by
            funext B
            exact div_eq_mul_inv _ _
          exact Eq.mp (congrArg (fun f : Matrix SpaceIndex SpaceIndex ℝ → ℝ =>
            HasFDerivAt f (0 : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] ℝ)
              (0 : Matrix SpaceIndex SpaceIndex ℝ)) hdiv.symm) hmulzero
        have hsum : HasFDerivAt
            (fun B : Matrix SpaceIndex SpaceIndex ℝ => B i j + (B.transpose * B) i j / 2)
            (source9CompletionEntryCLM i j) (0 : Matrix SpaceIndex SpaceIndex ℝ) := hadd he hhalf
        have hfun :
            (fun B : Matrix SpaceIndex SpaceIndex ℝ => source9OrthogonalCompletionMap B i j) =
            (fun B : Matrix SpaceIndex SpaceIndex ℝ => B i j + (B.transpose * B) i j / 2) := by
          funext B
          simp only [source9OrthogonalCompletionMap, ite_eq_right hij, ite_eq_right hji]
        exact Eq.mp (congrArg (fun f : Matrix SpaceIndex SpaceIndex ℝ → ℝ =>
          HasFDerivAt f (source9CompletionEntryCLM i j) (0 : Matrix SpaceIndex SpaceIndex ℝ))
          hfun.symm) hsum
  have hmatrix : HasFDerivAt source9OrthogonalCompletionMap
      (ContinuousLinearMap.pi (fun i : SpaceIndex =>
        ContinuousLinearMap.pi (fun j : SpaceIndex => source9CompletionEntryCLM i j)))
      (0 : Matrix SpaceIndex SpaceIndex ℝ) := by
    apply hasFDerivAt_pi.2
    intro i
    apply hasFDerivAt_pi.2
    intro j
    exact hentry i j
  have hoperator :
      (ContinuousLinearMap.pi (fun i : SpaceIndex =>
        ContinuousLinearMap.pi (fun j : SpaceIndex => source9CompletionEntryCLM i j)) :
          Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] Matrix SpaceIndex SpaceIndex ℝ) =
      ContinuousLinearMap.id ℝ (Matrix SpaceIndex SpaceIndex ℝ) := by
    apply ContinuousLinearMap.ext
    intro V
    rfl
  exact Eq.mp (congrArg
    (fun L : Matrix SpaceIndex SpaceIndex ℝ →L[ℝ] Matrix SpaceIndex SpaceIndex ℝ =>
      HasFDerivAt source9OrthogonalCompletionMap L (0 : Matrix SpaceIndex SpaceIndex ℝ))
    hoperator) hmatrix

theorem source9OrthogonalCompletionMap_fderiv_zero :
    fderiv ℝ source9OrthogonalCompletionMap 0 =
      ContinuousLinearMap.id ℝ (Matrix SpaceIndex SpaceIndex ℝ) :=
  source9OrthogonalCompletionMap_hasFDerivAt_zero.fderiv

theorem source9OrthogonalCompletionMap_hasStrictFDerivAt_zero :
    HasStrictFDerivAt source9OrthogonalCompletionMap
      (ContinuousLinearMap.id ℝ (Matrix SpaceIndex SpaceIndex ℝ)) 0 :=
  (source9OrthogonalCompletionMap_contDiff (1 : ℕ∞ω)).contDiffAt.hasStrictFDerivAt'
    source9OrthogonalCompletionMap_hasFDerivAt_zero one_ne_zero

#print axioms source9CompletionEntryCLM
#print axioms source9CompletionEntryCLM_apply
#print axioms source9CompletionGramEntry_contDiff
#print axioms source9CompletionGramEntry_hasFDerivAt_zero
#print axioms source9OrthogonalCompletionMap_contDiff
#print axioms source9OrthogonalCompletionMap_hasFDerivAt_zero
#print axioms source9OrthogonalCompletionMap_fderiv_zero
#print axioms source9OrthogonalCompletionMap_hasStrictFDerivAt_zero
end
end FCP.BFSSPairedSpin9Clifford
