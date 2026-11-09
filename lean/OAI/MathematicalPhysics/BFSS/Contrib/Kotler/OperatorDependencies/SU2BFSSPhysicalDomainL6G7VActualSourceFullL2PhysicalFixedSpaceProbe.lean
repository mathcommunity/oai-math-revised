import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7UActualSourceFullL2GaugeContractionProbe

/-!
L6G7V — the ORIGINAL BFSS physical Hilbert space is EXACTLY the
joint fixed-point space of the source-exact bounded SU(2) FullL2
gauge transformations U(g) := fiberAction(g) ∘ bosonPullback(g⁻¹).

Original GaugeCore defines physicalSpace as the intersection of
ker(bosonPullback(g) - fiberAction(g)) for all group elements.
The only new step here is identifying that defining equation with
fixedness under the ACTUAL combined FullL2 operator from L6G7U.
The fermionic inverse relation is proved directly from the already
qualified concrete GaugeData group homomorphism on Fermion 2 and
pinned Mathlib compLp ae semantics, not inserted as an assumption.

This is a bounded-operator/full physical Hilbert subspace identity.
It does NOT prove strong continuity, an unbounded generator domain,
any closure/self-adjointness, or spectral information.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace FCP.BFSSSU2PhysicalDomainL6G7V
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6G7U
open MeasureTheory

/-- True fermionic GaugeData fiberAction cancels its inverse ON the
original FullL2 2 space, using original Fock SU(2) representation. -/
theorem actualSourceFermionFiberAction_inv_cancel
    (g : GaugeGroup 2) (v : FullL2 2) :
    pairedGaugeData.fiberAction g
      (pairedGaugeData.fiberAction g⁻¹ v) = v := by
  apply Lp.ext_iff.mpr
  have ho := ContinuousLinearMap.coeFn_compLp
    (pairedGaugeData.fermion g).toContinuousLinearEquiv.toContinuousLinearMap
    (pairedGaugeData.fiberAction g⁻¹ v)
  have hi := ContinuousLinearMap.coeFn_compLp
    (pairedGaugeData.fermion g⁻¹).toContinuousLinearEquiv.toContinuousLinearMap v
  filter_upwards [ho, hi] with x houter hinner
  calc
    (pairedGaugeData.fiberAction g
      (pairedGaugeData.fiberAction g⁻¹ v)) x =
        pairedGaugeData.fermion g
          ((pairedGaugeData.fiberAction g⁻¹ v) x) := houter
    _ = pairedGaugeData.fermion g
          (pairedGaugeData.fermion g⁻¹ (v x)) := by
      -- #224: coeFn_compLp states its result in expanded compLp form.
      -- The source fiberAction is definitionally this same compLpₗ map,
      -- but `rw` does not reduce the packaged Lp term to find hinner.
      change (pairedGaugeData.fiberAction g⁻¹ v) x =
        pairedGaugeData.fermion g⁻¹ (v x) at hinner
      rw [hinner]
    _ = v x := by
      calc
        _ = pairedGaugeData.fermion (g * g⁻¹) (v x) := by
          rw [map_mul]
          rfl
        _ = v x := by simp

/-- Joint fixed vectors of the L6G7U original bounded FullL2
gauge operators are EXACTLY the pinned original GaugeCore.physicalSpace;
the implication in both directions needs only the source fermionic
inverse and the original all-groups physicalSpace equations. -/
theorem actualOriginalFullL2GaugePair_fixed_iff_physical
    (v : FullL2 2) :
    (∀ g : GaugeGroup 2, actualOriginalFullL2GaugePairCLM g v = v) ↔
      v ∈ pairedGaugeData.physicalSpace := by
  constructor
  · intro hfixed
    change v ∈ ⨅ g : GaugeGroup 2,
      LinearMap.ker (pairedGaugeData.bosonPullback g -
        pairedGaugeData.fiberAction g)
    rw [Submodule.mem_iInf]
    intro g
    change pairedGaugeData.bosonPullback g v -
      pairedGaugeData.fiberAction g v = 0
    have h := hfixed g⁻¹
    rw [actualOriginalFullL2GaugePairCLM_apply, inv_inv] at h
    have he := congrArg (pairedGaugeData.fiberAction g) h
    rw [actualSourceFermionFiberAction_inv_cancel] at he
    exact sub_eq_zero.mpr he
  · intro hphysical g
    have hm := (Submodule.mem_iInf _).mp hphysical g⁻¹
    have he : pairedGaugeData.bosonPullback g⁻¹ v =
        pairedGaugeData.fiberAction g⁻¹ v := by
      exact sub_eq_zero.mp hm
    rw [actualOriginalFullL2GaugePairCLM_apply, he]
    exact actualSourceFermionFiberAction_inv_cancel g v

#print axioms actualSourceFermionFiberAction_inv_cancel
#print axioms actualOriginalFullL2GaugePair_fixed_iff_physical
#check @actualOriginalFullL2GaugePair_fixed_iff_physical

end
end FCP.BFSSSU2PhysicalDomainL6G7V
