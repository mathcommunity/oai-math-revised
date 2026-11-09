import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6POriginalTransportedFockVacuumProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG1BColorAnnihilatorProbe

/-!
L6G6Q — the exact paired 48-source-Majorana color cancellation,
pointwise in each of the eight original spin pairs.

Unlike L6G6N/P, this target refers to the ACTUAL source AlgebraData 2
witness pairedAlgebraData.theta, with the accepted explicit
SpinIndex ≃ Fin 8 × Fin 2 and colorModeEquiv relabelings.

The prior 24-mode Fock vacuum cancellation is transferred into
each genuine source spin pair. The full 16-spin sum and literal
bounded source color-generator vacuum statement remain subsequent
finite-sum obligations, not assumptions or conclusions of this file.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G6Q
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSFermionF1 FCP.BFSSFermionF2
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2PhysicalDomainL6G6P

private abbrev s : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)

/-- Reuse the accepted G1B exact phase computation on the original
source F2 majorana1: the imaginary component is i(C-A), not i(C+A). -/
private theorem sourceMajorana1_phase (m : Fin 24) :
    majorana1 m = s • ((Complex.I : ℂ) • (creator m - annihilator m)) := by
  unfold majorana1
  simp only [star_smul, Complex.star_def, Complex.conj_I, creator_adjoint]
  rw [smul_sub, sub_eq_add_neg]
  ext x
  simp

/-- The literal pairedAlgebraData even spin field is the source
normalization of the creator-plus-annihilator of the exact color mode. -/
theorem sourcePairedTheta_even (j : Fin 8) (a : ColorIndex 2) :
    pairedAlgebraData.theta (spinPairEquiv.symm (j, (0 : Fin 2))) a =
      s • (creator (colorModeEquiv (j,a)) + annihilator (colorModeEquiv (j,a))) := by
  rw [pairedAlgebraData_theta, pairedTheta_even]
  rfl

/-- The literal pairedAlgebraData odd spin field has the complementary
source imaginary phase from accepted G1B. -/
theorem sourcePairedTheta_odd (j : Fin 8) (a : ColorIndex 2) :
    pairedAlgebraData.theta (spinPairEquiv.symm (j, (1 : Fin 2))) a =
      s • ((Complex.I : ℂ) •
        (creator (colorModeEquiv (j,a)) - annihilator (colorModeEquiv (j,a)))) := by
  rw [pairedAlgebraData_theta, pairedTheta_odd]
  exact sourceMajorana1_phase _

/-- At a fixed spin pair, distinct source colors name distinct exact
Fock modes; no unidentified index permutation is permitted. -/
theorem sourceColorMode_ne (j : Fin 8) {a b : ColorIndex 2} (hab : a ≠ b) :
    colorModeEquiv (j,a) ≠ colorModeEquiv (j,b) := by
  intro h
  exact hab (congrArg Prod.snd (colorModeEquiv.injective h))

/-- Actual original two-spin color cross term kills the transported
Fock vacuum at each paired spin j. No abstract CAR/vacuum assumption
remains: L6G6P discharged it on Fermion 2 in gate #129. -/
theorem sourcePairedTheta_twoSpin_vacuumCancellation
    (j : Fin 8) (a b : ColorIndex 2) (hab : a ≠ b) :
    ((pairedAlgebraData.theta (spinPairEquiv.symm (j, (0 : Fin 2))) a *
        pairedAlgebraData.theta (spinPairEquiv.symm (j, (0 : Fin 2))) b) +
      (pairedAlgebraData.theta (spinPairEquiv.symm (j, (1 : Fin 2))) a *
        pairedAlgebraData.theta (spinPairEquiv.symm (j, (1 : Fin 2))) b))
      source24ModeVacuum = 0 := by
  rw [sourcePairedTheta_even j a, sourcePairedTheta_even j b,
      sourcePairedTheta_odd j a, sourcePairedTheta_odd j b]
  exact source24ModeFockPair_vacuumCancellation
    s (colorModeEquiv (j,a)) (colorModeEquiv (j,b))
    (sourceColorMode_ne j hab)

#print axioms sourceMajorana1_phase
#print axioms sourcePairedTheta_even
#print axioms sourcePairedTheta_odd
#print axioms sourceColorMode_ne
#print axioms sourcePairedTheta_twoSpin_vacuumCancellation
#check @sourcePairedTheta_twoSpin_vacuumCancellation

end
end FCP.BFSSSU2PhysicalDomainL6G6Q
