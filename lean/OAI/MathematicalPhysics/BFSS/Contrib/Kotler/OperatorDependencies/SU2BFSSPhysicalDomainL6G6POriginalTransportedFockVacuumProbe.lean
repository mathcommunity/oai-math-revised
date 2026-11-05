import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6OOriginalExteriorFockVacuumProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2FermionF2Probe

/-!
L6G6P — actual source Fock-vacuum transport into Fermion 2.

The literal original 24-mode exterior-algebra unit is moved through
the source fockCoordinates 23 equivalence and accepted fockBFSSUnitary.
The same conjugation that defines F1.annihilator transports the
source Clifford-contraction vacuum identity to the original BFSS
Fermion 2 Hilbert type.

The original, source-defined creator/annihilator CAR then discharges
both explicit premises of the kernel-qualified L6G6N cancellation
theorem for distinct twenty-four-mode labels, not merely for an
abstract similarly shaped family.

No claim is made yet about equality with G4B.fermionVacuum,
the full pairedAlgebraData spin sum, or the SU(2) gauge generator.
Those require their own exact source identifications.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G6P
noncomputable section

open OAI.BFSSQuantum
open OAI.Laughlin.Fock
open OAI.ContinuumCoulomb.HubbardGlobal
open FCP.BFSSFermionF1
open FCP.BFSSFermionF2
open FCP.BFSSSU2PhysicalDomainL6G6O

/-- Exact 24-mode Fock vacuum, transported into the original source
Fermion 2 Hilbert type by the same maps used by accepted F1. -/
noncomputable def source24ModeVacuum : Fermion 2 :=
  fockBFSSUnitary (fockCoordinates 23 (1 : Space 23))

/-- The literal transferred, bounded source F1 annihilator kills
the exact transported Fock vacuum; no premise is supplied. -/
theorem source24ModeVacuum_annihilator (i : Fin 24) :
    annihilator i source24ModeVacuum = 0 := by
  change
    (fockBFSSUnitary.conjStarAlgEquiv
      (fockOperator (OAI.Laughlin.Fock.annihilate i)))
      (fockBFSSUnitary (fockCoordinates 23 (1 : Space 23))) = 0
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply, fockOperator_coordinates,
    original24ModeVacuum_annihilate, map_zero, map_zero]

/-- The already accepted source F2 off-diagonal mixed CAR,
specialized to distinct literal Fock mode labels. -/
private theorem source24Mode_offDiagonalMixedCAR
    (i j : Fin 24) (hij : i ≠ j) :
    annihilator i * creator j + creator j * annihilator i = 0 := by
  -- The continuous-linear-map smul is a concrete action, not the
  -- generic SMulZeroClass instance selected by zero_smul. Prove the
  -- zero operator pointwise using the source Hilbert-module action.
  have hzero :
      (0 : ℂ) • (1 : Fermion 2 →L[ℂ] Fermion 2) = 0 := by
    -- Generic 'ext x' also destructs the PiLp codomain into coordinates.
    -- Instead use exactly operator extensionality, retaining the vector goal.
    apply ContinuousLinearMap.ext
    intro x
    change (0 : ℂ) • ((1 : Fermion 2 →L[ℂ] Fermion 2) x) = 0
    simp
  simpa only [_root_.ite_eq_right hij, hzero] using
    (FCP.BFSSFermionF2.annihilator_creator_car i j)

/-- Exact source-Fock specialization of the qualified L6G6N
Majorana-phase cancellation on the real Fermion 2 Hilbert space.
The arbitrary common normalization q includes the actual source
sqrt(2)/2 value; equality with source pairedTheta is still separate. -/
theorem source24ModeFockPair_vacuumCancellation
    (q : ℂ) (i j : Fin 24) (hij : i ≠ j) :
    (((q • (creator i + annihilator i)) *
       (q • (creator j + annihilator j))) +
     ((q • (Complex.I • (creator i - annihilator i))) *
       (q • (Complex.I • (creator j - annihilator j)))))
      source24ModeVacuum = 0 := by
  exact
    FCP.BFSSSU2PhysicalDomainL6G6N.finiteFockMajoranaPair_vacuumCancellation
      creator annihilator source24ModeVacuum q
      source24ModeVacuum_annihilator
      (fun a b hab => source24Mode_offDiagonalMixedCAR a b hab)
      i j hij

#print axioms source24ModeVacuum
#print axioms source24ModeVacuum_annihilator
#print axioms source24Mode_offDiagonalMixedCAR
#print axioms source24ModeFockPair_vacuumCancellation
#check @source24ModeFockPair_vacuumCancellation

end
end FCP.BFSSSU2PhysicalDomainL6G6P
