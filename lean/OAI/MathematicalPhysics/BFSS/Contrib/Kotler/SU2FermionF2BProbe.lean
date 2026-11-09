import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2FermionF2Probe

/-!
# BFSS fermion F2-B1 — complementary Majorana normalized self-CAR

Builds on kernel-accepted F2-A (Gate #39) and the accepted 24-mode
Fock representation (Gate #36). This file proves the imaginary
Majorana's same-mode CAR without constructing a large matrix. Pairwise
different-mode Majorana CAR and theta_irreducible remain separate goals.
-/

namespace FCP.BFSSFermionF2B
noncomputable section

open FCP.BFSSFermionF1 FCP.BFSSFermionF2

private abbrev BFSSOp :=
  OAI.BFSSQuantum.Fermion 2 →L[ℂ] OAI.BFSSQuantum.Fermion 2

private def rotatedCreator (i : Fin 24) : BFSSOp :=
  Complex.I • creator i

private def rotatedAnnihilator (i : Fin 24) : BFSSOp :=
  star (rotatedCreator i)

private theorem rotatedAnnihilator_formula (i : Fin 24) :
    rotatedAnnihilator i = (-Complex.I : ℂ) • annihilator i := by
  simp only [rotatedAnnihilator, rotatedCreator, star_smul,
    Complex.star_def, Complex.conj_I, creator_adjoint]

private theorem rotatedCreator_sq (i : Fin 24) :
    rotatedCreator i * rotatedCreator i = 0 := by
  simp only [rotatedCreator, smul_mul_smul, creator_sq]
  ext x
  simp

private theorem rotatedAnnihilator_sq (i : Fin 24) :
    rotatedAnnihilator i * rotatedAnnihilator i = 0 := by
  simp only [rotatedAnnihilator_formula, smul_mul_smul, annihilator_sq]
  ext x
  simp

private theorem rotated_mixed_car (i : Fin 24) :
    rotatedAnnihilator i * rotatedCreator i +
      rotatedCreator i * rotatedAnnihilator i = (1 : BFSSOp) := by
  rw [rotatedAnnihilator_formula]
  change ((-Complex.I : ℂ) • annihilator i) * (Complex.I • creator i) +
    (Complex.I • creator i) * ((-Complex.I : ℂ) • annihilator i) = 1
  have hs : (-Complex.I : ℂ) * Complex.I = 1 := by
    rw [neg_mul, Complex.I_mul_I]
    norm_num
  have hs' : Complex.I * (-Complex.I : ℂ) = 1 := by
    rw [mul_comm]
    exact hs
  simpa only [smul_mul_smul, hs, hs', one_smul] using
    (creator_annihilator_car i)

private theorem majoranaScale_sq :
    (((Real.sqrt 2 / 2 : ℝ) : ℂ)) * (((Real.sqrt 2 / 2 : ℝ) : ℂ)) =
      (1 / 2 : ℂ) := by
  have hs : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have heq : (Real.sqrt 2 / 2 : ℝ) * (Real.sqrt 2 / 2 : ℝ) = 1 / 2 :=
    (pow_two _).symm.trans hs
  have hc := congrArg (fun x : ℝ => (x : ℂ)) heq
  simpa only [Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_one] using hc

/-- The second, imaginary Majorana has the exact BFSS delta-one normalization. -/
theorem majorana1_car (i : Fin 24) :
    majorana1 i * majorana1 i + majorana1 i * majorana1 i = (1 : BFSSOp) := by
  let c := rotatedCreator i
  let a := rotatedAnnihilator i
  have hcc : c * c = 0 := rotatedCreator_sq i
  have haa : a * a = 0 := rotatedAnnihilator_sq i
  have hca : a * c + c * a = 1 := rotated_mixed_car i
  have hsum : (c + a) * (c + a) = 1 := by
    calc
      _ = c * c + (a * c + c * a) + a * a := by noncomm_ring
      _ = 1 := by rw [hcc, haa, hca]; simp
  unfold majorana1
  change (_ • (c + a)) * (_ • (c + a)) +
    (_ • (c + a)) * (_ • (c + a)) = _
  simp only [smul_mul_smul, hsum, majoranaScale_sq]
  refine (add_smul (1 / 2 : ℂ) (1 / 2 : ℂ)
      (1 : BFSSOp)).symm.trans ?_
  have hcoef : (1 / 2 : ℂ) + (1 / 2 : ℂ) = 1 := by norm_num
  rw [hcoef, one_smul]

#print axioms majorana1_car

end
end FCP.BFSSFermionF2B

/-!
Independent BFSS SU(2) formalization contribution by Evan T. Kotler (2026).
Research DOI: https://doi.org/10.5281/zenodo.23291242
FCP source: b60baa806dab3f0b296229a78f70e07b787544ab, experiments/openai-math-su2-concrete-potential/SU2FermionF2BProbe.lean
Copyright (c) 2026 Evan T. Kotler. SPDX-License-Identifier: Apache-2.0.
Build status: integrated candidate; upstream port NOT YET independently verified.
OpenAI retains credit for the original BFSS definitions on which this work builds.
-/
