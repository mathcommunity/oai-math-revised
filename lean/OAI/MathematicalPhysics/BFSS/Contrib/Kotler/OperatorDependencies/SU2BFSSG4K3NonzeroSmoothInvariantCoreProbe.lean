import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K2BNonzeroPhysicalL2Probe

/-!
# BFSS SU(2) G4-K3 — nonzero smooth Gauss-invariant core witness

Gate #130 constructed a NONZERO concrete member of the literal
SU(2) Gauss physical Hilbert subspace, as a compactly supported
radial bump tensored with the exact 24-orbital fermionic singlet.

Here prove that this SAME physical L² state is the image under the
pinned upstream coreToL2 of an actual BFSS SmoothCore 2 test function,
which is itself a NONZERO member of pairedGaugeData.invariantCore.

The radial bump is smooth as a function of the NORM SQUARED;
there is no unsupported differentiation of the unsquared norm
at the origin. No energy eigenstate, Hamiltonian spectral bound,
supersymmetric ground state or physical BFSS prediction follows.
-/

namespace FCP.BFSSSU2GaugeG4K3
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open MeasureTheory
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG2A
open FCP.BFSSSU2GaugeG4B
open FCP.BFSSSU2GaugeG4E
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2GaugeG4K2A
open FCP.BFSSSU2GaugeG4K2B

/-- Smoothness on the ACTUAL Euclidean bosonic configuration space.
The input is ‖x‖² (smooth), not ‖x‖ (not smooth at zero). -/
theorem radialBumpProfile_contDiff :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (radialVacuumProfile radialBumpCoefficient) := by
  have hpoly :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : Boson 2 => (2 : ℝ) - 2 * ‖x‖ ^ 2) := by
    exact contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ))
  have hreal :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : Boson 2 => Real.smoothTransition (2 - 2 * ‖x‖ ^ 2)) :=
    Real.smoothTransition.contDiff.comp hpoly
  have hcomplex :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : Boson 2 =>
          (Real.smoothTransition (2 - 2 * ‖x‖ ^ 2) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hreal
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : Boson 2 =>
      (Real.smoothTransition (2 - 2 * ‖x‖ ^ 2) : ℂ) • fermionVacuum)
  exact hcomplex.smul
    (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : Boson 2 => fermionVacuum))

/-- The exact same nonzero physical radial wavepacket, now packaged
as a literal source-defined BFSS SmoothCore test function. -/
noncomputable def radialBumpSmoothCore : SmoothCore 2 where
  toFun := radialVacuumProfile radialBumpCoefficient
  contDiff' := radialBumpProfile_contDiff
  hasCompactSupport' := radialBumpProfile_hasCompactSupport
  tsupport_subset' := by
    intro x hx
    trivial

/-- Source-identity check: the pinned core-to-L² map sends the
new smooth core function to EXACTLY the Gate #130 physical state. -/
theorem radialBumpSmoothCore_toL2 :
    coreToL2 radialBumpSmoothCore = radialBumpL2 := by
  apply Lp.ext_iff.mpr
  exact (coreToL2_ae radialBumpSmoothCore).trans radialBumpL2_ae.symm

/-- The smooth test function is NONZERO, not only a formal
section in the BFSS SmoothCore type. -/
theorem radialBumpSmoothCore_ne_zero :
    radialBumpSmoothCore ≠ (0 : SmoothCore 2) := by
  intro hz
  have hzero : radialBumpL2 = 0 := by
    rw [← radialBumpSmoothCore_toL2, hz, map_zero]
  exact radialBumpL2_ne_zero hzero

/-- The literal upstream invariantCore membership is established
through the existing physicalSpace.comap coreToL2 definition. -/
theorem radialBumpSmoothCore_mem_invariantCore :
    radialBumpSmoothCore ∈ pairedGaugeData.invariantCore := by
  change coreToL2 radialBumpSmoothCore ∈ pairedGaugeData.physicalSpace
  rw [radialBumpSmoothCore_toL2]
  exact radialBumpL2_mem_physicalSpace

/-- A certified actual member of the exact BFSS Gauss-invariant
smooth core, not an unrelated smooth or pointwise-invariant field. -/
noncomputable def radialBumpInvariantCore : pairedGaugeData.invariantCore :=
  ⟨radialBumpSmoothCore, radialBumpSmoothCore_mem_invariantCore⟩

/-- The genuine pinned BFSS invariant smooth core is NONZERO. -/
theorem radialBumpInvariantCore_ne_zero :
    radialBumpInvariantCore ≠ 0 := by
  intro hz
  have hval := congrArg
    (fun f : pairedGaugeData.invariantCore => (f.val : SmoothCore 2)) hz
  change radialBumpSmoothCore = 0 at hval
  exact radialBumpSmoothCore_ne_zero hval

/-- The actual smooth invariant witness obeys literal pointwise
Gauss equivariance on both the bosonic and fermionic factors. -/
theorem radialBumpInvariantCore_equivariant
    (g : GaugeGroup 2) (x : Boson 2) :
    radialBumpSmoothCore (bosonGauge g x) =
      fermionGaugeUnitaryHom g (radialBumpSmoothCore x) := by
  change radialBumpInvariantCore.val (pairedGaugeData.boson g x) =
    pairedGaugeData.fermion g (radialBumpInvariantCore.val x)
  exact pairedGaugeData.invariantCore_equivariant radialBumpInvariantCore g x

/-- The upstream supersymmetric charge quadratic form is defined
on this NONZERO smooth invariant test state and is nonnegative.
This is NOT a claim it vanishes or that the test state minimizes
the Hamiltonian or belongs to an operator eigen-domain. -/
theorem radialBumpSmoothCore_coreForm_nonneg :
    0 ≤ pairedAlgebraData.coreForm radialBumpSmoothCore :=
  pairedAlgebraData.coreForm_nonneg radialBumpSmoothCore

#print axioms radialBumpProfile_contDiff
#print axioms radialBumpSmoothCore
#print axioms radialBumpSmoothCore_toL2
#print axioms radialBumpSmoothCore_ne_zero
#print axioms radialBumpSmoothCore_mem_invariantCore
#print axioms radialBumpInvariantCore
#print axioms radialBumpInvariantCore_ne_zero
#print axioms radialBumpInvariantCore_equivariant
#print axioms radialBumpSmoothCore_coreForm_nonneg

end
end FCP.BFSSSU2GaugeG4K3
