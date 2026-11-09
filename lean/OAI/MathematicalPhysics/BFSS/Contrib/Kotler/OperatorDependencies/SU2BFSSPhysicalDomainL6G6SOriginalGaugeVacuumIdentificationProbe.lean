import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6RSourceSpinSumColorGeneratorVacuumProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4BFermionLinearTransportProbe

/-!
L6G6S — identify the *same* original BFSS Fock vacuum in source
fermionic generator construction and genuine exterior SU(2) gauge action.

The construction fockAlgebraToBFSS in accepted G4B is definitionally
the composite of the same Fock-coordinate linear equivalence and
fockBFSSUnitary used by the source L6G6P proof. This file formalizes
the equality between the two presented vacuum vectors, transfers
the accepted exterior-gauge action's vacuum invariance to the original
L6G6P vector, and applies the accepted L6G6R color-generator
annihilation at the exact G4B fermionVacuum.

This does NOT identify infinitesimal generators. Equality of the
vector killed by J_F and fixed by the representation is necessary
but is insufficient by itself to establish the derivative identity.
No Gauss constraint, supercharge, or spectrum claim is made.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G6S
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4B
open FCP.BFSSSU2PhysicalDomainL6G6P
open FCP.BFSSSU2PhysicalDomainL6G6R

/-- Both original source presentations use exactly the same complex
FockCoordinates 23 → FockBFSSUnitary transport of the exterior unit. -/
theorem source24ModeVacuum_eq_actualGaugeVacuum :
    source24ModeVacuum = fermionVacuum := by
  rfl

/-- The actual G4B exterior-algebra SU(2) fermionic gauge action fixes
the precise original Fock vacuum used by the L6G6P/R source theorem. -/
theorem actualGaugeAction_fixes_source24ModeVacuum
    (g : GaugeGroup 2) :
    fermionGaugeLinearEquiv g source24ModeVacuum =
      source24ModeVacuum := by
  rw [source24ModeVacuum_eq_actualGaugeVacuum]
  exact fermionGaugeLinearEquiv_vacuum g

/-- The actual bounded original color generator annihilates the
vacuum of the genuine constructed gauge representation, not merely
an unrelated similarly named vacuum. -/
theorem sourcePairedFermionColorGenerator_actualGaugeVacuum
    (c : ColorIndex 2) :
    FCP.BFSSSU2PhysicalDomainL6G6K.sourceFiberFermionColorGenerator
      pairedAlgebraData c fermionVacuum = 0 := by
  rw [← source24ModeVacuum_eq_actualGaugeVacuum]
  exact sourcePairedFermionColorGenerator_vacuum c

#print axioms source24ModeVacuum_eq_actualGaugeVacuum
#print axioms actualGaugeAction_fixes_source24ModeVacuum
#print axioms sourcePairedFermionColorGenerator_actualGaugeVacuum
#check @sourcePairedFermionColorGenerator_actualGaugeVacuum

end
end FCP.BFSSSU2PhysicalDomainL6G6S
