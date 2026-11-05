import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1GExactSourceRelativeCharacterTrivialityProbe

/-!
S1H: EXACT source covariant gauge representation uniqueness.

Given any multiplicative representation of the ORIGINAL gauge group SU(2)
on the ORIGINAL source Fermion 2 linear-equivalence module, with the
EXPLICIT 48-Majorana color covariance hV from S1D/S1G, the representation
is the original fermionGaugeLinearHom, not merely equal up to a phase.

These statements are immediate kernel-checked consequences of previously
qualified S1D.relativeGaugeScalar_apply and S1G.original_relativeGaugeScalar_trivial.
There is NO asserted existence or identification of an independent Cl(48)
manuscript module, no Hilbert-unitary transport, and no spectrum result.
-/

set_option autoImplicit false
set_option maxHeartbeats 180000

namespace FCP.BFSSSU2PhysicalDomainS1H
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4B
open FCP.BFSSSU2PhysicalDomainS1D
open FCP.BFSSSU2PhysicalDomainS1G

variable (V : GaugeGroup 2 →* (Fermion 2 ≃ₗ[ℂ] Fermion 2))
variable (hV : ∀ (g : GaugeGroup 2) (α : SpinIndex)
  (A : ColorIndex 2) (v : Fermion 2),
  V g (pairedTheta α A v) =
    ∑ B : ColorIndex 2,
      (pairedAlgebraData.adjointCoefficient g A B : ℂ) •
        pairedTheta α B (V g v))

-- Force the explicit covariance premise into each subsequent theorem's context.
-- Lean otherwise omits section variables absent from their result types.
include hV

/-- Every same-covariant source gauge implementation agrees on each
literal source Fermion 2 vector, with no residual scalar ambiguity. -/
theorem original_source_implementer_unique_apply
    (g : GaugeGroup 2) (v : Fermion 2) :
    V g v = fermionGaugeLinearEquiv g v := by
  calc
    V g v = relativeGaugeScalar V hV g • fermionGaugeLinearEquiv g v :=
      relativeGaugeScalar_apply V hV g v
    _ = fermionGaugeLinearEquiv g v := by
      rw [original_relativeGaugeScalar_trivial V hV g, one_smul]

/-- Equality holds at the complete invertible linear operator level. -/
theorem original_source_implementer_unique
    (g : GaugeGroup 2) :
    V g = fermionGaugeLinearEquiv g := by
  apply LinearEquiv.ext
  intro v
  exact original_source_implementer_unique_apply V hV g v

/-- The actual group homomorphism itself is unique among source
48-theta covariant group representations. -/
theorem original_source_gauge_representation_unique :
    V = fermionGaugeLinearHom := by
  apply MonoidHom.ext
  intro g
  exact original_source_implementer_unique V hV g

#print axioms original_source_implementer_unique_apply
#print axioms original_source_implementer_unique
#print axioms original_source_gauge_representation_unique

end
end FCP.BFSSSU2PhysicalDomainS1H
