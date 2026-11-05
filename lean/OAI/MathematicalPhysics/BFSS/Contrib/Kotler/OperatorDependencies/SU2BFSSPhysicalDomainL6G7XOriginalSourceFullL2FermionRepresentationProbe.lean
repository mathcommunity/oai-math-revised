import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7WActualSourceFullL2GaugeIsometryProbe

/-!
L6G7X — the EXACT original fermionic GaugeData.fiberAction on
original BFSS FullL2 is a finite SU2 group action.

Lift the already source-qualified fermionGaugeUnitaryHom group law
to the literal pinned GaugeCore FullL2 fiberAction using Mathlib's
Lp coeFn_compLp almost-everywhere semantics, WITHOUT assuming
the combined boson/fermion U(g) representation law.

This provides independent, source-faithful L2 group/identity
algebra ahead of full U(g)U(h)=U(gh). Strong continuity,
infinitesimal L2 generator domains, and spectra remain OPEN.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace FCP.BFSSSU2PhysicalDomainL6G7X
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG4J
open MeasureTheory

/-- The ACTUAL fermion SU2 representation acts multiplicatively
when lifted to the original FullL2 Hilbert space via source fiberAction.
No change of bosonic or fermionic source convention. -/
theorem actualSourceFullL2_fiberAction_mul
    (g h : GaugeGroup 2) (v : FullL2 2) :
    pairedGaugeData.fiberAction g
      (pairedGaugeData.fiberAction h v) =
        pairedGaugeData.fiberAction (g * h) v := by
  apply Lp.ext_iff.mpr
  have ho := ContinuousLinearMap.coeFn_compLp
    (pairedGaugeData.fermion g).toContinuousLinearEquiv.toContinuousLinearMap
    (pairedGaugeData.fiberAction h v)
  have hi := ContinuousLinearMap.coeFn_compLp
    (pairedGaugeData.fermion h).toContinuousLinearEquiv.toContinuousLinearMap v
  have hp := ContinuousLinearMap.coeFn_compLp
    (pairedGaugeData.fermion (g * h)).toContinuousLinearEquiv.toContinuousLinearMap v
  filter_upwards [ho, hi, hp] with x houter hinner hprod
  calc
    (pairedGaugeData.fiberAction g
      (pairedGaugeData.fiberAction h v)) x =
        pairedGaugeData.fermion g ((pairedGaugeData.fiberAction h v) x) :=
          houter
    _ = pairedGaugeData.fermion g
          (pairedGaugeData.fermion h (v x)) := by
      change (pairedGaugeData.fiberAction h v) x =
        pairedGaugeData.fermion h (v x) at hinner
      rw [hinner]
    _ = pairedGaugeData.fermion (g * h) (v x) := by
      rw [map_mul]
      rfl
    _ = (pairedGaugeData.fiberAction (g * h) v) x := by
      change (pairedGaugeData.fiberAction (g * h) v) x =
        pairedGaugeData.fermion (g * h) (v x) at hprod
      exact hprod.symm

/-- The original fermionic gauge identity acts as the identity
on the genuine BFSS FullL2, not a proxy finite-Fock space. -/
theorem actualSourceFullL2_fiberAction_one
    (v : FullL2 2) :
    pairedGaugeData.fiberAction (1 : GaugeGroup 2) v = v := by
  apply Lp.ext_iff.mpr
  have h := ContinuousLinearMap.coeFn_compLp
    (pairedGaugeData.fermion (1 : GaugeGroup 2)).toContinuousLinearEquiv.toContinuousLinearMap v
  filter_upwards [h] with x hx
  calc
    (pairedGaugeData.fiberAction (1 : GaugeGroup 2) v) x =
      pairedGaugeData.fermion (1 : GaugeGroup 2) (v x) := hx
    _ = v x := by simp

#print axioms actualSourceFullL2_fiberAction_mul
#print axioms actualSourceFullL2_fiberAction_one
#check @actualSourceFullL2_fiberAction_mul
#check @actualSourceFullL2_fiberAction_one

end
end FCP.BFSSSU2PhysicalDomainL6G7X
