import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5AOriginalKineticGramProbe

/-!
# L6G5B — source complex kinetic weights and color Gram contraction

The unchanged L6G4B kinetic coefficient has a genuine -Complex.I and a
color selector. This gate contracts exactly those coefficients and connects
them to the kernel-qualified L6G5A real-gamma Gram theorem.

A visible gamma-field equality relates an arbitrary AlgebraData to the
exact original gamma construction. The concrete source pairedAlgebraData
satisfies this equality definitionally; its separate specialization can
be performed without changing the coefficient theorem.

No kinetic differential-operator square, quartic potential, Gauss,
physical restriction, closure or spectrum is established here.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G5B
noncomputable section
open scoped Matrix BigOperators
open OAI.BFSSGamma
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G2
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G4A
open FCP.BFSSSU2PhysicalDomainL6G4B
open FCP.BFSSSU2PhysicalDomainL6G5A
open FCP.BFSSSU2PhysicalDomainL6G1

/-- All sixteen real spinor labels weight the *exact* source -i kinetic
coefficient, including its unchanged color Kronecker selector. -/
def sourceSpinorKineticWeight {N : ℕ} (M : AlgebraData N)
    (w : SpinIndex → ℝ) (p : FermionLabel N) (u : BosonLabel N) : ℂ :=
  ∑ α : SpinIndex, (w α : ℂ) * sourceKineticWeight M α p u

/-- Identify the literal source kinetic coefficient with its original
complex gamma row. The gamma equality is an explicit, testable premise. -/
theorem sourceSpinorKineticWeight_eq {N : ℕ} (M : AlgebraData N)
    (w : SpinIndex → ℝ)
    (hgamma : M.gamma = originalGamma)
    (p : FermionLabel N) (u : BosonLabel N) :
    sourceSpinorKineticWeight M w p u =
      if u.2 = p.2 then
        -Complex.I * (((w ᵥ* originalGamma u.1) p.1 : ℝ) : ℂ)
      else 0 := by
  classical
  unfold sourceSpinorKineticWeight sourceKineticWeight
  by_cases h : u.2 = p.2
  · simp only [_root_.ite_eq_left h]
    calc
      (∑ α : SpinIndex,
        (w α : ℂ) * (-Complex.I * ((M.gamma u.1 α p.1 : ℝ) : ℂ))) =
        -Complex.I *
          (∑ α : SpinIndex, ((w α * originalGamma u.1 α p.1 : ℝ) : ℂ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro α _
          rw [hgamma]
          push_cast
          ring
      _ = _ := by
          congr 1
          change (∑ α : SpinIndex,
              ((w α * originalGamma u.1 α p.1 : ℝ) : ℂ)) =
            (((∑ α : SpinIndex, w α * originalGamma u.1 α p.1 : ℝ) : ℝ) : ℂ)
          simp
  · simp only [_root_.ite_eq_right h, mul_zero, Finset.sum_const_zero]

/-- Real source Gram transported to complex scalar weights. This is an
ordinary ring-hom transport of the accepted L6G5A theorem. -/
theorem originalGamma_complexRowKineticGram (w : Spin → ℝ)
    (i j : Space) :
    (∑ β : Spin,
      (((w ᵥ* originalGamma i) β : ℝ) : ℂ) *
      (((w ᵥ* originalGamma j) β : ℝ) : ℂ)) =
      if i = j then (spinorSquareNorm w : ℂ) else 0 := by
  have h := originalGamma_rowKineticGram w i j
  change (∑ β : Spin,
    (w ᵥ* originalGamma i) β * (w ᵥ* originalGamma j) β) =
      if i = j then spinorSquareNorm w else 0 at h
  have hc := congrArg (fun a : ℝ => (a : ℂ)) h
  by_cases hij : i = j
  · simp only [_root_.ite_eq_left hij] at hc ⊢
    -- Normalize the cast of the finite real sum and its products.
    simpa using hc
  · simp only [_root_.ite_eq_right hij] at hc ⊢
    simpa using hc

/-- Color contraction of two selectors does not assume or change
the number of colors. -/
private theorem colorSelectors_contract {S C : Type*}
    [Fintype S] [Fintype C] [DecidableEq C]
    (a b : C) (F G : S → ℂ) :
    (∑ p : S × C,
      (if a = p.2 then F p.1 else 0) *
      (if b = p.2 then G p.1 else 0)) =
        if a = b then (∑ s : S, F s * G s) else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  by_cases hab : a = b
  · subst b
    have heq (s : S) (c : C) :
        (if a = c then F s else 0) * (if a = c then G s else 0) =
          if a = c then F s * G s else 0 := by
      by_cases hac : a = c <;> simp [hac]
    simp_rw [heq]
    simp
  · have hz (s : S) (c : C) :
        (if a = c then F s else 0) * (if b = c then G s else 0) = 0 := by
      by_cases hac : a = c
      · subst c
        have hba : b ≠ a := Ne.symm hab
        simp [hba]
      · simp [hac]
    simp_rw [hz]
    simp [hab]

private theorem minusI_mul_minusI (a b : ℂ) :
    (-Complex.I * a) * (-Complex.I * b) = -(a * b) := by
  calc
    _ = (Complex.I * Complex.I) * (a * b) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

/-- Full spinor-plus-color contraction for the exact complex source
kinetic weights. The two -i factors give the negative Laplacian sign;
both position labels must match for the Gram to be nonzero. -/
theorem sourceSpinorKineticWeight_colorGram {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ)
    (hgamma : M.gamma = originalGamma)
    (u v : BosonLabel N) :
    (∑ p : FermionLabel N,
      sourceSpinorKineticWeight M w p u *
      sourceSpinorKineticWeight M w p v) =
        if u = v then -(spinorSquareNorm w : ℂ) else 0 := by
  classical
  simp_rw [sourceSpinorKineticWeight_eq M w hgamma]
  have hcolor := colorSelectors_contract
    (S := SpinIndex) (C := ColorIndex N)
    u.2 v.2
    (fun r => -Complex.I * (((w ᵥ* originalGamma u.1) r : ℝ) : ℂ))
    (fun r => -Complex.I * (((w ᵥ* originalGamma v.1) r : ℝ) : ℂ))
  rw [hcolor]
  by_cases hc : u.2 = v.2
  · simp only [_root_.ite_eq_left hc]
    simp_rw [minusI_mul_minusI]
    rw [Finset.sum_neg_distrib, originalGamma_complexRowKineticGram]
    by_cases hs : u.1 = v.1
    · have huv : u = v := Prod.ext hs hc
      simp [huv]
    · have hne : u ≠ v := fun heq => hs (congrArg Prod.fst heq)
      simp [hs, hne]
  · have hne : u ≠ v := fun heq => hc (congrArg Prod.snd heq)
    simp [hc, hne]

#print axioms sourceSpinorKineticWeight_eq
#print axioms originalGamma_complexRowKineticGram
#print axioms colorSelectors_contract
#print axioms minusI_mul_minusI
#print axioms sourceSpinorKineticWeight_colorGram
#check @sourceSpinorKineticWeight_colorGram

end
end FCP.BFSSSU2PhysicalDomainL6G5B
