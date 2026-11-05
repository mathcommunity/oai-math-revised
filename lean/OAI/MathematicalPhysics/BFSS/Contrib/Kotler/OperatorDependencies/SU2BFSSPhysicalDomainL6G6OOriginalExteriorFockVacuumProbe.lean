import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6NAbstractFockPairVacuumCancellationProbe
import OAI.Analysis.Laughlin.Operators.CAR

/-!
L6G6O — actual pinned exterior-Fock vacuum annihilation.

The vacuum here is the literal unit of the upstream exterior algebra
OAI.Laughlin.Fock.Space Q; annihilate is the *source-defined*
Clifford contraction by coordinate projection. The proof uses the
contraction of the exterior unit, not an assumed vacuum premise.

The accepted Fock-to-BFSS transport and pairedAlgebraData specialization
remain separate, explicit obligations. This step must not be described
as proof that the concrete source color generator kills the transported
BFSS vacuum.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G6O
noncomputable section

open OAI.Laughlin.Fock

/-- Every original source contraction kills the exterior-algebra unit.
The statement is valid at every finite orbital count. -/
theorem originalExteriorVacuum_annihilate (Q : ℕ) (i : Fin (Q + 1)) :
    annihilate i (1 : Space Q) = 0 := by
  change CliffordAlgebra.contractLeft (LinearMap.proj i) (1 : Space Q) = 0
  simp

/-- Specialize to the original twenty-four Fock modes (Q=23). -/
theorem original24ModeVacuum_annihilate (i : Fin 24) :
    annihilate i (1 : Space 23) = 0 :=
  originalExteriorVacuum_annihilate 23 i

#print axioms originalExteriorVacuum_annihilate
#print axioms original24ModeVacuum_annihilate
#check @original24ModeVacuum_annihilate

end
end FCP.BFSSSU2PhysicalDomainL6G6O
