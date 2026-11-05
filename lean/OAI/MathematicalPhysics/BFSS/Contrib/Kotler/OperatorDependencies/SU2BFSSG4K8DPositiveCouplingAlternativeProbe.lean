import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K8CZeroParameterChargeProbe

/-!
# BFSS SU(2) G4-K8D — positive interacting two-coupling nonvanishing

Gate #147 formally establishes that every exact FIRST-ORDER kinetic
spin charge is nonzero in FullL2 on our genuine compactly supported
SU(2) Gauss-invariant physical radial trial state.

In the original pinned OAI.BFSSQuantum.AlgebraData, the
DEFORMED REAL POTENTIAL FIELD with m=0 is linear in coupling h.
We compare the two STRICTLY POSITIVE couplings h=1 and h=2.
The source core-charge identity Q(2,0)+K = 2 Q(1,0) implies that
BOTH exact interacting charge images CANNOT vanish, because
Gate #147 already proved K is nonzero in the real source L².

The conclusion is a finite ALTERNATIVE for the SAME state,
for EACH of the genuine 16 spin components, not a proof that
the standard h=1 charge specifically is nonzero. It implies
E(1,0)>0 OR E(2,0)>0 by Gate #138's proved strict positivity iff.
It says nothing about h>0 with m>0, any ground state,
self-adjoint spectral gap or full BFSS Hamiltonian spectrum.

No auxiliary Hamiltonian, free-only parameter trick or
abstract replacement operator is introduced.
-/

namespace FCP.BFSSSU2GaugeG4K8D
noncomputable section

open scoped BigOperators
open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4K2B
open FCP.BFSSSU2GaugeG4K3
open FCP.BFSSSU2GaugeG4K6
open FCP.BFSSSU2GaugeG4K7
open FCP.BFSSSU2GaugeG4K8C

/-- For zero mass, the original source potential field at
coupling 2 is twice the SAME source field at coupling 1.
Derive from pinned deformedRealField_polarized, not a
newly postulated parameter-scaling law. -/
theorem physicalRealField_two_eq_twice_one
    (α : SpinIndex) (x : Boson 2) :
    pairedAlgebraData.deformedRealField 2 0 α x =
      (2 : ℝ) • pairedAlgebraData.deformedRealField 1 0 α x := by
  rw [pairedAlgebraData.deformedRealField_polarized,
    pairedAlgebraData.deformedRealField_polarized]
  apply ContinuousLinearMap.ext
  intro z
  simp [IsSMulApply.smul_apply]

/-- Transport source potential-field scaling to the ACTUAL
SmoothCore multiplier operators at our original physical
state, preserving the original field smoothness witnesses. -/
theorem physicalCoreField_two_eq_twice_one (α : SpinIndex) :
    MixedEnergy.field
      (pairedAlgebraData.deformedRealField 2 0 α)
      (pairedAlgebraData.deformedRealField_contDiff 2 0 α)
      radialBumpSmoothCore =
    (2 : ℝ) • MixedEnergy.field
      (pairedAlgebraData.deformedRealField 1 0 α)
      (pairedAlgebraData.deformedRealField_contDiff 1 0 α)
      radialBumpSmoothCore := by
  apply DFunLike.ext
  intro x
  simp only [MixedEnergy.field_apply, smul_apply]
  rw [physicalRealField_two_eq_twice_one]
  simp only [IsSMulApply.smul_apply]

/-- Pinned exact interacting core operator identity at the
TWO positive couplings: Q(2,0)+K=2 Q(1,0).
No symmetry or cancellation assumption is used. -/
theorem physicalCharge_two_plus_kinetic_eq_twice_one (α : SpinIndex) :
    pairedAlgebraData.deformedCoreCharge 2 0 α radialBumpSmoothCore +
      MixedEnergy.firstOrder
        (pairedAlgebraData.kineticSkewSymbol α) radialBumpSmoothCore =
    (2 : ℝ) •
      pairedAlgebraData.deformedCoreCharge 1 0 α radialBumpSmoothCore := by
  calc
    pairedAlgebraData.deformedCoreCharge 2 0 α radialBumpSmoothCore +
        MixedEnergy.firstOrder
          (pairedAlgebraData.kineticSkewSymbol α) radialBumpSmoothCore =
      (MixedEnergy.firstOrder
          (pairedAlgebraData.kineticSkewSymbol α) radialBumpSmoothCore +
        MixedEnergy.field
          (pairedAlgebraData.deformedRealField 2 0 α)
          (pairedAlgebraData.deformedRealField_contDiff 2 0 α)
          radialBumpSmoothCore) +
      MixedEnergy.firstOrder
        (pairedAlgebraData.kineticSkewSymbol α) radialBumpSmoothCore := rfl
    _ =
      (MixedEnergy.firstOrder
          (pairedAlgebraData.kineticSkewSymbol α) radialBumpSmoothCore +
        (2 : ℝ) • MixedEnergy.field
          (pairedAlgebraData.deformedRealField 1 0 α)
          (pairedAlgebraData.deformedRealField_contDiff 1 0 α)
          radialBumpSmoothCore) +
      MixedEnergy.firstOrder
        (pairedAlgebraData.kineticSkewSymbol α) radialBumpSmoothCore := by
        rw [physicalCoreField_two_eq_twice_one]
    _ = (2 : ℝ) •
        (MixedEnergy.firstOrder
          (pairedAlgebraData.kineticSkewSymbol α) radialBumpSmoothCore +
        MixedEnergy.field
          (pairedAlgebraData.deformedRealField 1 0 α)
          (pairedAlgebraData.deformedRealField_contDiff 1 0 α)
          radialBumpSmoothCore) := by module
    _ = (2 : ℝ) •
        pairedAlgebraData.deformedCoreCharge 1 0 α radialBumpSmoothCore := rfl

/-- FOR EACH genuine source spin component, its interacting
FullL2 charge at h=1,m=0 or h=2,m=0 is nonzero.
Both cannot vanish, as that would force the previously
compiled genuine kinetic charge to vanish. -/
theorem physicalInteractingCharge_one_or_two_ne_zero (α : SpinIndex) :
    coreToL2
        (pairedAlgebraData.deformedCoreCharge 1 0 α radialBumpSmoothCore) ≠ 0 ∨
    coreToL2
        (pairedAlgebraData.deformedCoreCharge 2 0 α radialBumpSmoothCore) ≠ 0 := by
  by_contra hn
  have h1 :
      coreToL2
        (pairedAlgebraData.deformedCoreCharge 1 0 α radialBumpSmoothCore) = 0 := by
    by_contra h
    exact hn (Or.inl h)
  have h2 :
      coreToL2
        (pairedAlgebraData.deformedCoreCharge 2 0 α radialBumpSmoothCore) = 0 := by
    by_contra h
    exact hn (Or.inr h)
  have htwo (f : SmoothCore 2) : (2 : ℝ) • f = f + f := by module
  have hid := congrArg (fun f : SmoothCore 2 => coreToL2 f)
    (physicalCharge_two_plus_kinetic_eq_twice_one α)
  rw [map_add, htwo, map_add, h1, h2, zero_add, add_zero] at hid
  exact (physicalKineticFirstOrder_L2_ne_zero α) hid

/-- Strictly positive ACTUAL source-defined interacting
trial energy at one of TWO positive h values, with m=0.
This proves a finite alternative, NOT specifically h=1,
nor positive mass, nor a spectral gap. -/
theorem physicalInteractingTrialEnergy_one_or_two_pos :
    0 < physicalDeformedEnergy 1 0 ∨
      0 < physicalDeformedEnergy 2 0 := by
  obtain h1 | h2 := physicalInteractingCharge_one_or_two_ne_zero (0 : SpinIndex)
  · exact Or.inl ((physicalDeformedEnergy_pos_iff 1 0).mpr ⟨0, h1⟩)
  · exact Or.inr ((physicalDeformedEnergy_pos_iff 2 0).mpr ⟨0, h2⟩)

#print axioms physicalRealField_two_eq_twice_one
#print axioms physicalCoreField_two_eq_twice_one
#print axioms physicalCharge_two_plus_kinetic_eq_twice_one
#print axioms physicalInteractingCharge_one_or_two_ne_zero
#print axioms physicalInteractingTrialEnergy_one_or_two_pos

end
end FCP.BFSSSU2GaugeG4K8D
