import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2FermionF2B2ImagProbe

/-!
# BFSS fermions F2-B2c1 — off-diagonal mixed Majorana CAR

This bounded gate proves real/imaginary anticommutation for distinct
Fock modes on the exact BFSSQuantum.Fermion 2 representation. It uses
only accepted all-mode Fock creation/annihilation CAR, phase transport,
and the definitions of normalized real/imaginary Majoranas.

Same-mode mixed anticommutation remains a separate F2-B2c2 obligation.
Full 48-label theta_CAR and irreducibility are not established here.
-/

namespace FCP.BFSSFermionF2B2Mixed
noncomputable section

open FCP.BFSSFermionF1 FCP.BFSSFermionF2

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

/-- Distinct-mode real and imaginary Majoranas anticommute exactly. -/
theorem majorana01_car_ne (i j : Fin 24) (hij : i ≠ j) :
    majorana0 i * majorana1 j + majorana1 j * majorana0 i =
      (0 : BFSSOp) := by
  have hji : j ≠ i := Ne.symm hij
  have hcc0 : creator i * creator j + creator j * creator i =
      (0 : BFSSOp) := creator_creator_car i j
  have haa0 : annihilator i * annihilator j + annihilator j * annihilator i =
      (0 : BFSSOp) := annihilator_annihilator_car i j
  have hac0 : annihilator i * creator j + creator j * annihilator i =
      (0 : BFSSOp) := by
    calc
      _ = (0 : ℂ) • (1 : BFSSOp) := by
        simpa only [hij, ite_false] using (annihilator_creator_car i j)
      _ = 0 := by
        ext x
        simp
  have hca0 : creator i * annihilator j + annihilator j * creator i =
      (0 : BFSSOp) := by
    have h : annihilator j * creator i + creator i * annihilator j =
        (0 : BFSSOp) := by
      calc
        _ = (0 : ℂ) • (1 : BFSSOp) := by
          simpa only [hji, ite_false] using (annihilator_creator_car j i)
        _ = 0 := by
          ext x
          simp
    calc
      _ = annihilator j * creator i + creator i * annihilator j := add_comm _ _
      _ = 0 := h
  have hcc : creator i * rotatedC j + rotatedC j * creator i =
      (0 : BFSSOp) := by
    simpa only [rotatedC, one_smul] using
      (phase_car_zero (1 : ℂ) (Complex.I : ℂ) (creator i) (creator j) hcc0)
  have haa : annihilator i * rotatedA j + rotatedA j * annihilator i =
      (0 : BFSSOp) := by
    simpa only [rotatedA, one_smul] using
      (phase_car_zero (1 : ℂ) (-Complex.I : ℂ)
        (annihilator i) (annihilator j) haa0)
  have hac : annihilator i * rotatedC j + rotatedC j * annihilator i =
      (0 : BFSSOp) := by
    simpa only [rotatedC, one_smul] using
      (phase_car_zero (1 : ℂ) (Complex.I : ℂ) (annihilator i) (creator j) hac0)
  have hca : creator i * rotatedA j + rotatedA j * creator i =
      (0 : BFSSOp) := by
    simpa only [rotatedA, one_smul] using
      (phase_car_zero (1 : ℂ) (-Complex.I : ℂ) (creator i) (annihilator j) hca0)
  have hsum :
      (creator i + annihilator i) * (rotatedC j + rotatedA j) +
        (rotatedC j + rotatedA j) * (creator i + annihilator i) =
          (0 : BFSSOp) := by
    calc
      _ = (creator i * rotatedC j + rotatedC j * creator i) +
            (annihilator i * rotatedA j + rotatedA j * annihilator i) +
            (annihilator i * rotatedC j + rotatedC j * annihilator i) +
            (creator i * rotatedA j + rotatedA j * creator i) := by
              noncomm_ring
      _ = 0 := by rw [hcc, haa, hac, hca]; simp
  simp only [majorana0, majorana1_expanded]
  let s : ℂ :=
    (((Real.sqrt 2 / 2 : ℝ) : ℂ)) * (((Real.sqrt 2 / 2 : ℝ) : ℂ))
  let p : BFSSOp := (creator i + annihilator i) * (rotatedC j + rotatedA j)
  let q : BFSSOp := (rotatedC j + rotatedA j) * (creator i + annihilator i)
  rw [smul_mul_smul, smul_mul_smul]
  change s • p + s • q = (0 : BFSSOp)
  calc
    s • p + s • q = s • (p + q) := (smul_add s p q).symm
    _ = s • (0 : BFSSOp) :=
      congrArg (fun T : BFSSOp => s • T) hsum
    _ = 0 := by
      ext x
      simp

#print axioms majorana01_car_ne

end
end FCP.BFSSFermionF2B2Mixed

/-!
Independent BFSS SU(2) formalization contribution by Evan T. Kotler (2026).
Research DOI: https://doi.org/10.5281/zenodo.23291242
FCP source: b60baa806dab3f0b296229a78f70e07b787544ab, experiments/openai-math-su2-concrete-potential/SU2FermionF2B2MixedProbe.lean
Copyright (c) 2026 Evan T. Kotler. SPDX-License-Identifier: Apache-2.0.
Build status: integrated candidate; upstream port NOT YET independently verified.
OpenAI retains credit for the original BFSS definitions on which this work builds.
-/
