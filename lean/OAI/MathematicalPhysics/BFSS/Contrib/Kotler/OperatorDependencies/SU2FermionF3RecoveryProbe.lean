import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2FermionF3InvariantProbe

/-!
# BFSS fermions F3-A2 — recovery of Fock creation/annihilation invariance

Gate #58 verified that theta-invariance on the exact BFSS Fermion 2 space
implies invariance under both normalized Majorana components at each mode.

This bounded step recovers invariance under the accepted transported creator
and annihilator, using their actual (sqrt 2)/2 normalization and the imaginary
phase. It does not assert or assume that an invariant submodule is trivial.
Occupation-basis generation and theta_irreducible remain future obligations.

This is a compiler candidate, not a claim of kernel acceptance.
-/

namespace FCP.BFSSFermionF3A2
noncomputable section

open FCP.BFSSFermionF1 FCP.BFSSFermionF2 FCP.BFSSFermionF3

private abbrev BFSSFermion := OAI.BFSSQuantum.Fermion 2

/-- The phase formula follows from the exact accepted definition of majorana1. -/
private theorem majorana1_phase (i : Fin 24) :
    majorana1 i =
      (((Real.sqrt 2 / 2 : ℝ) : ℂ)) •
        ((Complex.I : ℂ) • (creator i - annihilator i)) := by
  unfold majorana1
  simp only [star_smul, Complex.star_def, Complex.conj_I, creator_adjoint]
  rw [smul_sub, sub_eq_add_neg]
  ext x
  simp

/-- On the exact 24-mode BFSS Fock realization, stability under every theta
implies stability under every transported creator and annihilator. -/
theorem thetaInvariant_creator_annihilator
    (W : Submodule ℂ BFSSFermion)
    (hθ : ∀ α A, ∀ w ∈ W, thetaCandidate α A w ∈ W) :
    (∀ i : Fin 24, ∀ w ∈ W, creator i w ∈ W) ∧
      (∀ i : Fin 24, ∀ w ∈ W, annihilator i w ∈ W) := by
  have hcomponents := thetaInvariant_majoranaComponents W hθ
  have hboth (i : Fin 24) (w : BFSSFermion) (hw : w ∈ W) :
      creator i w ∈ W ∧ annihilator i w ∈ W := by
    let s : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)
    have hsReal : (Real.sqrt 2 / 2 : ℝ) ≠ 0 := by
      exact ne_of_gt (div_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
        (by norm_num : (0 : ℝ) < 2))
    have hs : s ≠ 0 := by
      change ((Real.sqrt 2 / 2 : ℝ) : ℂ) ≠ 0
      exact_mod_cast hsReal

    have hm0 := hcomponents.1 i w hw
    change (s • (creator i + annihilator i)) w ∈ W at hm0
    have hm1 := hcomponents.2 i w hw
    rw [majorana1_phase i] at hm1
    change (s • ((Complex.I : ℂ) • (creator i - annihilator i))) w ∈ W at hm1

    have hsumScaled : s • ((creator i + annihilator i) w) ∈ W := by
      simpa only [_root_.smul_apply] using hm0
    have hdiffScaled :
        s • ((Complex.I : ℂ) • ((creator i - annihilator i) w)) ∈ W := by
      simpa only [_root_.smul_apply] using hm1

    have hsum : (creator i + annihilator i) w ∈ W := by
      have h := W.smul_mem s⁻¹ hsumScaled
      have hInv : s⁻¹ * s = 1 := inv_mul_cancel₀ hs
      simpa only [smul_smul, hInv, one_smul] using h
    have hphase : (Complex.I : ℂ) • ((creator i - annihilator i) w) ∈ W := by
      have h := W.smul_mem s⁻¹ hdiffScaled
      have hInv : s⁻¹ * s = 1 := inv_mul_cancel₀ hs
      have hcancel : s⁻¹ * (s * Complex.I) = Complex.I := by
        rw [← mul_assoc, hInv, one_mul]
      simpa only [smul_smul, hcancel] using h
    have hdiff : (creator i - annihilator i) w ∈ W := by
      have h := W.smul_mem ((Complex.I : ℂ)⁻¹) hphase
      have hInv : (Complex.I : ℂ)⁻¹ * Complex.I = 1 :=
        inv_mul_cancel₀ Complex.I_ne_zero
      simpa only [smul_smul, hInv, one_smul] using h

    have hplus : creator i w + annihilator i w ∈ W := by
      simpa only [_root_.add_apply] using hsum
    have hminus : creator i w - annihilator i w ∈ W := by
      simpa only [_root_.sub_apply] using hdiff

    have hTwoCreator : (2 : ℂ) • (creator i w) ∈ W := by
      have h := W.add_mem hplus hminus
      have hEq : (creator i w + annihilator i w) +
          (creator i w - annihilator i w) = (2 : ℂ) • creator i w := by
        rw [two_smul]
        abel
      exact hEq ▸ h
    have hTwoAnnihilator : (2 : ℂ) • (annihilator i w) ∈ W := by
      have h := W.sub_mem hplus hminus
      have hEq : (creator i w + annihilator i w) -
          (creator i w - annihilator i w) = (2 : ℂ) • annihilator i w := by
        rw [two_smul]
        abel
      exact hEq ▸ h

    have hHalf : (1 / 2 : ℂ) * 2 = 1 := by norm_num
    constructor
    · have h := W.smul_mem (1 / 2 : ℂ) hTwoCreator
      simpa only [smul_smul, hHalf, one_smul] using h
    · have h := W.smul_mem (1 / 2 : ℂ) hTwoAnnihilator
      simpa only [smul_smul, hHalf, one_smul] using h
  constructor
  · intro i w hw
    exact (hboth i w hw).1
  · intro i w hw
    exact (hboth i w hw).2

#print axioms thetaInvariant_creator_annihilator

end
end FCP.BFSSFermionF3A2
