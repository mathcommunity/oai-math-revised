import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K8E2KineticOddParityProbe

/-!
# BFSS SU(2) G4-K8E3 — original interacting smooth-core charge noncancellation

At the accepted Gates #155/#157, the original radial smooth Gauss-invariant
SU2 state has even actual source massless interaction field and odd actual
source kinetic first-order field. Gate #147 proves the kinetic charge
is nonzero as an original L² section.

This prospective stage proves, by a generic real-linear parity
separation, that the ORIGINAL source interacting deformedCoreCharge
cannot be the ZERO SMOOTH-CORE SECTION for ANY real h at zero mass,
hence not at h=1.

It does NOT yet prove that its L² equivalence class is nonzero:
a separate continuity/full-support injection argument will be needed
before strict interacting trial energy can be concluded. No spectral gap,
ground state or infimum is claimed.
-/

namespace FCP.BFSSSU2GaugeG4K8E3
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4K3
open FCP.BFSSSU2GaugeG4K8C
open FCP.BFSSSU2GaugeG4K8E1
open FCP.BFSSSU2GaugeG4K8E2

/-- Abstract smooth-core parity separation: a nonzero odd section
cannot be canceled pointwise by an even section. No BFSS operator
is expanded inside this generic algebraic proof. -/
private theorem abstractOddEvenSum_ne_zero
    (k v : SmoothCore 2)
    (hkodd : ∀ x : Boson 2, k (-x) = -(k x))
    (hveven : ∀ x : Boson 2, v (-x) = v x)
    (hk : k ≠ 0) :
    k + v ≠ 0 := by
  intro hzero
  apply hk
  apply DFunLike.ext
  intro x
  have hpos : k x + v x = 0 := by
    have heval := congrArg (fun f : SmoothCore 2 => f x) hzero
    simpa only [add_apply, zero_apply] using heval
  have hneg : -(k x) + v x = 0 := by
    have heval := congrArg (fun f : SmoothCore 2 => f (-x)) hzero
    have hval : k (-x) + v (-x) = 0 := by
      simpa only [add_apply, zero_apply] using heval
    rw [hkodd x, hveven x] at hval
    exact hval
  have htwice : k x + k x = 0 := by
    calc
      k x + k x = (k x + v x) - (-(k x) + v x) := by abel
      _ = 0 := by rw [hpos, hneg]; simp
  have hsmul : (2 : ℝ) • k x = 0 := by
    rw [two_smul]
    exact htwice
  exact (smul_eq_zero.mp hsmul).resolve_left (by norm_num)

/-- The genuine source first-order core cannot be the zero section:
otherwise its image under the actual coreToL2 map would vanish,
contradicting the independently compiled Gate #147 L² result. -/
theorem physicalKineticFirstOrder_core_ne_zero (α : SpinIndex) :
    MixedEnergy.firstOrder
      (pairedAlgebraData.kineticSkewSymbol α) radialBumpSmoothCore ≠ 0 := by
  intro hz
  apply physicalKineticFirstOrder_L2_ne_zero α
  have hL2 := congrArg (fun f : SmoothCore 2 => coreToL2 f) hz
  simpa only [map_zero] using hL2

/-- No exact pointwise cancellation of the real source BFSS
kinetic and source MASSLESS interacting potential contributions
on the original smooth physical radial state, for any real h. -/
theorem physicalInteractingCoreCharge_massless_ne_zero
    (h : ℝ) (α : SpinIndex) :
    pairedAlgebraData.deformedCoreCharge h 0 α radialBumpSmoothCore ≠ 0 := by
  have hsum :
      MixedEnergy.firstOrder
          (pairedAlgebraData.kineticSkewSymbol α) radialBumpSmoothCore +
        MixedEnergy.field
          (pairedAlgebraData.deformedRealField h 0 α)
          (pairedAlgebraData.deformedRealField_contDiff h 0 α)
          radialBumpSmoothCore ≠ 0 :=
    abstractOddEvenSum_ne_zero
      (MixedEnergy.firstOrder
        (pairedAlgebraData.kineticSkewSymbol α) radialBumpSmoothCore)
      (MixedEnergy.field
        (pairedAlgebraData.deformedRealField h 0 α)
        (pairedAlgebraData.deformedRealField_contDiff h 0 α)
        radialBumpSmoothCore)
      (physicalKineticFirstOrder_odd α)
      (physicalMasslessCorePotential_even h α)
      (physicalKineticFirstOrder_core_ne_zero α)
  intro hz
  apply hsum
  change
    MixedEnergy.firstOrder
        (pairedAlgebraData.kineticSkewSymbol α) radialBumpSmoothCore +
      MixedEnergy.field
        (pairedAlgebraData.deformedRealField h 0 α)
        (pairedAlgebraData.deformedRealField_contDiff h 0 α)
        radialBumpSmoothCore = 0 at hz
  exact hz

/-- Specifically h=1, m=0, the ORIGINAL interacting source
charge is a nonzero smooth-core section for every genuine spin α.
This is NOT yet a theorem of nonzero L² charge. -/
theorem physicalInteractingCoreCharge_one_ne_zero (α : SpinIndex) :
    pairedAlgebraData.deformedCoreCharge 1 0 α radialBumpSmoothCore ≠ 0 :=
  physicalInteractingCoreCharge_massless_ne_zero 1 α

#print axioms abstractOddEvenSum_ne_zero
#print axioms physicalKineticFirstOrder_core_ne_zero
#print axioms physicalInteractingCoreCharge_massless_ne_zero
#print axioms physicalInteractingCoreCharge_one_ne_zero

end
end FCP.BFSSSU2GaugeG4K8E3
