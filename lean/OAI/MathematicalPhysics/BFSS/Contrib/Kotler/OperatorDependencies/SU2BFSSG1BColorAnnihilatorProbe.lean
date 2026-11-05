import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG1APairedThetaProbe

/-!
# BFSS SU(2) G1-B — manuscript-normalized color-specific annihilators

The new pairedAlgebraData has a definite spin-pair and color-to-Fock-mode
labeling (G1-A, Gate #87). This file identifies its actual continuous
linear theta fields with each preexisting 24-mode Fock annihilator.

No SU(2) gauge action, gauge invariance or spectral theorem is claimed.
-/

namespace FCP.BFSSSU2GaugeG1B
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSFermionF1 FCP.BFSSFermionF2
open FCP.BFSSSU2GaugeG1A

private abbrev s : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)

/-- Exact normalization from the accepted Majorana definitions. -/
private theorem s_sq : s * s = (1 / 2 : ℂ) := by
  have hs : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hs
  simpa only [s, pow_two, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_one] using hc

/-- The imaginary self-adjoint Majorana is i times creator minus
annihilator; this is the actual phase in the pinned Fock construction. -/
private theorem majorana1_phase (m : Fin 24) :
    majorana1 m = s • ((Complex.I : ℂ) • (creator m - annihilator m)) := by
  unfold majorana1
  simp only [star_smul, Complex.star_def, Complex.conj_I, creator_adjoint]
  rw [smul_sub, sub_eq_add_neg]
  ext x
  simp

private theorem s_I_sq :
    s * (Complex.I * (s * Complex.I)) = -(1 / 2 : ℂ) := by
  calc
    _ = (s * s) * (Complex.I * Complex.I) := by ring
    _ = -(1 / 2 : ℂ) := by rw [s_sq, Complex.I_mul_I]; ring

/-- For each of the eight spin pairs and three colors, the manuscript's
complex combination is EXACTLY the genuine accepted Fock annihilator,
as equality of complex continuous linear operators on Fermion 2. -/
theorem color_annihilator (j : Fin 8) (A : ColorIndex 2) :
    annihilator (colorModeEquiv (j,A)) =
      s • (pairedTheta (spinPairEquiv.symm (j, (0 : Fin 2))) A +
        Complex.I • pairedTheta (spinPairEquiv.symm (j, (1 : Fin 2))) A) := by
  rw [pairedTheta_even, pairedTheta_odd, majorana1_phase]
  change annihilator (colorModeEquiv (j,A)) =
    s • (s • (creator (colorModeEquiv (j,A)) +
      annihilator (colorModeEquiv (j,A))) +
      Complex.I • (s • (Complex.I • (creator (colorModeEquiv (j,A)) -
        annihilator (colorModeEquiv (j,A))))))
  symm
  calc
    _ = (s * s) • (creator (colorModeEquiv (j,A)) +
          annihilator (colorModeEquiv (j,A))) +
        (s * (Complex.I * (s * Complex.I))) •
          (creator (colorModeEquiv (j,A)) -
            annihilator (colorModeEquiv (j,A))) := by
              simp only [smul_add, smul_smul]
    _ = (1 / 2 : ℂ) • (creator (colorModeEquiv (j,A)) +
          annihilator (colorModeEquiv (j,A))) -
        (1 / 2 : ℂ) • (creator (colorModeEquiv (j,A)) -
          annihilator (colorModeEquiv (j,A))) := by
            rw [s_sq, s_I_sq]
            have hneg :
                (-(1 / 2 : ℂ)) •
                    (creator (colorModeEquiv (j,A)) -
                      annihilator (colorModeEquiv (j,A))) =
                  -((1 / 2 : ℂ) •
                    (creator (colorModeEquiv (j,A)) -
                      annihilator (colorModeEquiv (j,A)))) :=
              neg_smul (1 / 2 : ℂ)
                (creator (colorModeEquiv (j,A)) -
                  annihilator (colorModeEquiv (j,A)))
            rw [hneg]
            exact (sub_eq_add_neg _ _).symm
    _ = annihilator (colorModeEquiv (j,A)) := by
      calc
        _ = (1 / 2 : ℂ) • annihilator (colorModeEquiv (j,A)) +
              (1 / 2 : ℂ) • annihilator (colorModeEquiv (j,A)) := by
                rw [smul_add, smul_sub]
                abel
        _ = annihilator (colorModeEquiv (j,A)) := by
          calc
            _ = ((1 / 2 : ℂ) + (1 / 2 : ℂ)) •
                  annihilator (colorModeEquiv (j,A)) :=
              (add_smul (1 / 2 : ℂ) (1 / 2 : ℂ)
                (annihilator (colorModeEquiv (j,A)))).symm
            _ = annihilator (colorModeEquiv (j,A)) := by norm_num

/-- The same identity for the actual theta field of the SECOND
fully constructed upstream AlgebraData 2 witness, not merely an
external similarly labeled theta function. -/
theorem pairedAlgebraData_color_annihilator (j : Fin 8) (A : ColorIndex 2) :
    annihilator (colorModeEquiv (j,A)) =
      s • (pairedAlgebraData.theta (spinPairEquiv.symm (j, (0 : Fin 2))) A +
        Complex.I •
          pairedAlgebraData.theta (spinPairEquiv.symm (j, (1 : Fin 2))) A) := by
  simpa only [pairedAlgebraData_theta] using color_annihilator j A

#print axioms color_annihilator
#print axioms pairedAlgebraData_color_annihilator

end
end FCP.BFSSSU2GaugeG1B
