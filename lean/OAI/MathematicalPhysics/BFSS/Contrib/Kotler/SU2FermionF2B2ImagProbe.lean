import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2FermionF2B2Probe

/-!
# BFSS fermions F2-B2b — imaginary Majorana all-mode CAR

Adds the 24×24 imaginary/imaginary pairwise CAR, independent of the
accepted F2-B2a real/real theorem. Phase-rotated creator/annihilator
identities are derived from F2-A without assumptions, and same-mode
normalization is the accepted F2-B1 theorem. Mixed real/imaginary
CAR, all-label theta_CAR, and irreducibility remain distinct goals.
-/

namespace FCP.BFSSFermionF2B2Imag
noncomputable section

open FCP.BFSSFermionF1 FCP.BFSSFermionF2 FCP.BFSSFermionF2B

private abbrev BFSSOp :=
  OAI.BFSSQuantum.Fermion 2 →L[ℂ] OAI.BFSSQuantum.Fermion 2

private def rotatedC (i : Fin 24) : BFSSOp :=
  (Complex.I : ℂ) • creator i

private def rotatedA (i : Fin 24) : BFSSOp :=
  (-Complex.I : ℂ) • annihilator i

private theorem majorana1_expanded (i : Fin 24) :
    majorana1 i =
      (((Real.sqrt 2 / 2 : ℝ) : ℂ)) • (rotatedC i + rotatedA i) := by
  unfold majorana1 rotatedC rotatedA
  simp only [star_smul, Complex.star_def, Complex.conj_I, creator_adjoint]

/-- Compatible phases preserve a zero anticommutator on exact BFSS operators. -/
private theorem phase_car_zero (a b : ℂ) (u v : BFSSOp)
    (h : u * v + v * u = (0 : BFSSOp)) :
    (a • u) * (b • v) + (b • v) * (a • u) = (0 : BFSSOp) := by
  calc
    _ = (a * b) • (u * v) + (b * a) • (v * u) := by
      rw [smul_mul_smul, smul_mul_smul]
    _ = (a * b) • (u * v) + (a * b) • (v * u) := by
      rw [mul_comm b a]
    _ = (a * b) • (u * v + v * u) :=
      (smul_add (a * b) (u * v) (v * u)).symm
    _ = (a * b) • (0 : BFSSOp) :=
      congrArg (fun T : BFSSOp => (a * b) • T) h
    _ = 0 := by
      ext x
      simp

/-- The imaginary 24-mode Majoranas obey the exact delta-one CAR. -/
theorem majorana1_car_all (i j : Fin 24) :
    majorana1 i * majorana1 j + majorana1 j * majorana1 i =
      (if i = j then (1 : ℂ) else 0) • (1 : BFSSOp) := by
  by_cases hij : i = j
  · subst j
    simpa only [eq_self, ite_true, one_smul] using (majorana1_car i)
  · have hji : j ≠ i := Ne.symm hij
    have hcc : rotatedC i * rotatedC j + rotatedC j * rotatedC i =
        (0 : BFSSOp) := by
      exact phase_car_zero (Complex.I : ℂ) (Complex.I : ℂ)
        (creator i) (creator j) (creator_creator_car i j)
    have haa : rotatedA i * rotatedA j + rotatedA j * rotatedA i =
        (0 : BFSSOp) := by
      exact phase_car_zero (-Complex.I : ℂ) (-Complex.I : ℂ)
        (annihilator i) (annihilator j) (annihilator_annihilator_car i j)
    have hac0 : annihilator i * creator j + creator j * annihilator i =
        (0 : BFSSOp) := by
      calc
        _ = (0 : ℂ) • (1 : BFSSOp) := by
          simpa only [hij, ite_false] using (annihilator_creator_car i j)
        _ = 0 := by
          ext x
          simp
    have hca0 : annihilator j * creator i + creator i * annihilator j =
        (0 : BFSSOp) := by
      calc
        _ = (0 : ℂ) • (1 : BFSSOp) := by
          simpa only [hji, ite_false] using (annihilator_creator_car j i)
        _ = 0 := by
          ext x
          simp
    have hac : rotatedA i * rotatedC j + rotatedC j * rotatedA i =
        (0 : BFSSOp) := by
      exact phase_car_zero (-Complex.I : ℂ) (Complex.I : ℂ)
        (annihilator i) (creator j) hac0
    have hca : rotatedA j * rotatedC i + rotatedC i * rotatedA j =
        (0 : BFSSOp) := by
      exact phase_car_zero (-Complex.I : ℂ) (Complex.I : ℂ)
        (annihilator j) (creator i) hca0
    have hsum :
        (rotatedC i + rotatedA i) * (rotatedC j + rotatedA j) +
          (rotatedC j + rotatedA j) * (rotatedC i + rotatedA i) =
            (0 : BFSSOp) := by
      calc
        _ = (rotatedC i * rotatedC j + rotatedC j * rotatedC i) +
              (rotatedA i * rotatedA j + rotatedA j * rotatedA i) +
              (rotatedA i * rotatedC j + rotatedC j * rotatedA i) +
              (rotatedA j * rotatedC i + rotatedC i * rotatedA j) := by
                noncomm_ring
        _ = 0 := by rw [hcc, haa, hac, hca]; simp
    simp only [hij, ite_false, majorana1_expanded]
    let s : ℂ :=
      (((Real.sqrt 2 / 2 : ℝ) : ℂ)) * (((Real.sqrt 2 / 2 : ℝ) : ℂ))
    let p : BFSSOp := (rotatedC i + rotatedA i) * (rotatedC j + rotatedA j)
    let q : BFSSOp := (rotatedC j + rotatedA j) * (rotatedC i + rotatedA i)
    rw [smul_mul_smul, smul_mul_smul]
    change s • p + s • q = (0 : ℂ) • (1 : BFSSOp)
    calc
      s • p + s • q = s • (p + q) := (smul_add s p q).symm
      _ = s • (0 : BFSSOp) := congrArg (fun T : BFSSOp => s • T) hsum
      _ = (0 : ℂ) • (1 : BFSSOp) := by
        ext x
        simp

#print axioms majorana1_car_all

end
end FCP.BFSSFermionF2B2Imag

/-!
Independent BFSS SU(2) formalization contribution by Evan T. Kotler (2026).
Research DOI: https://doi.org/10.5281/zenodo.23291242
FCP source: b60baa806dab3f0b296229a78f70e07b787544ab, experiments/openai-math-su2-concrete-potential/SU2FermionF2B2ImagProbe.lean
Copyright (c) 2026 Evan T. Kotler. SPDX-License-Identifier: Apache-2.0.
Build status: integrated candidate; upstream port NOT YET independently verified.
OpenAI retains credit for the original BFSS definitions on which this work builds.
-/
