import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2FermionF2B2MixedProbe

/-!
# BFSS fermions F2-B2c2 — same-mode mixed Majorana CAR

Complements F2-B2c1 (distinct modes): for each of the 24 Fock modes,
the normalized real and imaginary Majorana components anticommute.
The cancellation rests on the accepted creator/annihilator square-zero
lemmas, not an assumption of the desired Majorana CAR.

Combining cases into the all-pair mixed CAR and the 48-label theta
transport are deliberately separate, future proof gates.
-/

namespace FCP.BFSSFermionF2B2MixedDiag
noncomputable section

open FCP.BFSSFermionF1 FCP.BFSSFermionF2

private abbrev BFSSOp :=
  OAI.BFSSQuantum.Fermion 2 →L[ℂ] OAI.BFSSQuantum.Fermion 2

private theorem majorana1_phase (i : Fin 24) :
    majorana1 i =
      (((Real.sqrt 2 / 2 : ℝ) : ℂ)) •
        ((Complex.I : ℂ) • (creator i - annihilator i)) := by
  unfold majorana1
  simp only [star_smul, Complex.star_def, Complex.conj_I, creator_adjoint]
  rw [smul_sub, sub_eq_add_neg]
  ext x
  simp

/-- Same-mode real/imaginary CAR follows from creation and
annihilation square zero, with no new assumptions. -/
theorem majorana01_car_self (i : Fin 24) :
    majorana0 i * majorana1 i + majorana1 i * majorana0 i =
      (0 : BFSSOp) := by
  let c : BFSSOp := creator i
  let a : BFSSOp := annihilator i
  have hcc : c * c = (0 : BFSSOp) := creator_sq i
  have haa : a * a = (0 : BFSSOp) := annihilator_sq i
  have hbase :
      (c + a) * (c - a) + (c - a) * (c + a) =
        (0 : BFSSOp) := by
    calc
      _ = (c * c + c * c) - (a * a + a * a) := by
        simp only [mul_sub, sub_mul, mul_add, add_mul]
        abel
      _ = 0 := by rw [hcc, haa]; simp
  have hphase :
      (c + a) * ((Complex.I : ℂ) • (c - a)) +
        ((Complex.I : ℂ) • (c - a)) * (c + a) =
          (0 : BFSSOp) := by
    calc
      _ = (Complex.I : ℂ) • ((c + a) * (c - a)) +
            (Complex.I : ℂ) • ((c - a) * (c + a)) := by
              rw [mul_smul_comm, smul_mul_assoc]
      _ = (Complex.I : ℂ) •
            ((c + a) * (c - a) + (c - a) * (c + a)) :=
              (smul_add (Complex.I : ℂ)
                ((c + a) * (c - a)) ((c - a) * (c + a))).symm
      _ = (Complex.I : ℂ) • (0 : BFSSOp) :=
            congrArg (fun T : BFSSOp => (Complex.I : ℂ) • T) hbase
      _ = 0 := by
        ext x
        simp
  rw [majorana1_phase i]
  unfold majorana0
  let s : ℂ :=
    (((Real.sqrt 2 / 2 : ℝ) : ℂ)) * (((Real.sqrt 2 / 2 : ℝ) : ℂ))
  let p : BFSSOp := (c + a) * ((Complex.I : ℂ) • (c - a))
  let q : BFSSOp := ((Complex.I : ℂ) • (c - a)) * (c + a)
  rw [smul_mul_smul, smul_mul_smul]
  change s • p + s • q = (0 : BFSSOp)
  calc
    s • p + s • q = s • (p + q) := (smul_add s p q).symm
    _ = s • (0 : BFSSOp) :=
      congrArg (fun T : BFSSOp => s • T) hphase
    _ = 0 := by
      ext x
      simp

#print axioms majorana01_car_self

end
end FCP.BFSSFermionF2B2MixedDiag

/-!
Independent BFSS SU(2) formalization contribution by Evan T. Kotler (2026).
Research DOI: https://doi.org/10.5281/zenodo.23291242
FCP source: b60baa806dab3f0b296229a78f70e07b787544ab, experiments/openai-math-su2-concrete-potential/SU2FermionF2B2MixedDiagProbe.lean
Copyright (c) 2026 Evan T. Kotler. SPDX-License-Identifier: Apache-2.0.
Build status: integrated candidate; upstream port NOT YET independently verified.
OpenAI retains credit for the original BFSS definitions on which this work builds.
-/
