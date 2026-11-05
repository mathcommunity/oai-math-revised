import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6QPairedSourceThetaVacuumProbe

/-!
L6G6R — exact original 16-spin source fermionic color-generator vacuum.

The original source spin index has sixteen components. The accepted
explicit equivalence SpinIndex ≃ Fin 8 × Fin 2 partitions it into
eight exactly paired real/imaginary Majoranas, with unchanged colors
and normalization. The source L6G6Q two-spin cancellation is summed
over these eight pairs to discharge the literal L6G6M premise.

No abstract vacuum or CAR hypothesis remains, and no 2^24-matrix
expansion is used. This is the *original bounded fermionic color
generator* on the Fermion 2 fiber. Identification with the derivative
of the actual SU(2) gauge representation, and therefore the full Gauss
constraint, remains a separate obligation. No spectral conclusion.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G6R
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2PhysicalDomainL6G6P
open FCP.BFSSSU2PhysicalDomainL6G6Q

/-- The actual original source 16-spin theta quadratic expression
annihilates the exact 24-mode transported Fock vacuum for different
colors. This closes the literal pairCancellation premise from L6G6M. -/
theorem sourcePairedTheta_spinSum_vacuumCancellation
    (a b : ColorIndex 2) (hab : a ≠ b) :
    (∑ α : SpinIndex,
      (pairedAlgebraData.theta α a * pairedAlgebraData.theta α b)
        source24ModeVacuum) = 0 := by
  classical
  let F : SpinIndex → Fermion 2 := fun α =>
    (pairedAlgebraData.theta α a * pairedAlgebraData.theta α b)
      source24ModeVacuum
  have hreindex :
      (∑ α : SpinIndex, F α) =
        ∑ j : Fin 8,
          (F (spinPairEquiv.symm (j, (0 : Fin 2))) +
           F (spinPairEquiv.symm (j, (1 : Fin 2)))) := by
    calc
      _ = ∑ p : Fin 8 × Fin 2, F (spinPairEquiv.symm p) :=
        (Equiv.sum_comp spinPairEquiv.symm F).symm
      _ = ∑ j : Fin 8,
          (F (spinPairEquiv.symm (j, (0 : Fin 2))) +
           F (spinPairEquiv.symm (j, (1 : Fin 2)))) := by
        simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  change (∑ α : SpinIndex, F α) = 0
  rw [hreindex]
  apply Finset.sum_eq_zero
  intro j _
  dsimp [F]
  simpa only [_root_.add_apply] using
    (sourcePairedTheta_twoSpin_vacuumCancellation j a b hab)

/-- The L6G6M source interface becomes an unconditional theorem for
the actual accepted pairedAlgebraData, with no free Fock-vacuum or
mixed-CAR assumptions. The generator is precisely the previously
defined sourceFiberFermionColorGenerator, not a surrogate. -/
theorem sourcePairedFermionColorGenerator_vacuum
    (c : ColorIndex 2) :
    FCP.BFSSSU2PhysicalDomainL6G6K.sourceFiberFermionColorGenerator
      pairedAlgebraData c source24ModeVacuum = 0 := by
  have hcolor : ∀ a : ColorIndex 2,
      pairedAlgebraData.color a = FCP.BFSSSU2.normalizedPauli a := by
    intro a
    calc
      pairedAlgebraData.color a =
        FCP.BFSSSU2Full.concreteAlgebraData.color a :=
          pairedAlgebraData_color a
      _ = FCP.BFSSSU2.normalizedPauli a :=
          FCP.BFSSSU2Full.concreteAlgebraData_color a
  exact
    FCP.BFSSSU2PhysicalDomainL6G6M.sourceFiberFermionColorGenerator_vacuum_of_pairCancellation
      pairedAlgebraData hcolor c source24ModeVacuum
      (fun a b hab => sourcePairedTheta_spinSum_vacuumCancellation a b hab)

#print axioms sourcePairedTheta_spinSum_vacuumCancellation
#print axioms sourcePairedFermionColorGenerator_vacuum
#check @sourcePairedFermionColorGenerator_vacuum

end
end FCP.BFSSSU2PhysicalDomainL6G6R
