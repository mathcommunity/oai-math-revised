import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K2ANonzeroVacuumRadialProfileProbe

/-!
# BFSS SU(2) G4-K2B — concrete nonzero Gauss-invariant L² state

Construct a genuinely square-integrable nonzero radial bosonic
wavepacket tensored with the exact SU(2)-invariant, nonzero fermionic
Fock vacuum from Gate #129. Unlike the earlier pointwise profile,
this is a proof about the actual upstream BFSS FullL2 2 Hilbert space.

The scalar bump is continuous with compact support inside the
unit ball, and equals one at the origin. Its L² equivalence class
is nonzero by a.e.-to-everywhere uniqueness for continuous maps
under Euclidean volume. Membership in the LITERAL Gauss physical
submodule uses the true Lp measure-preserving pullback and the
true fiberwise unitary action. No alternate state space or
unproved gauge-invariance hypothesis is permitted.

This does NOT imply any state is a BFSS energy eigenstate, bound
state, Hamiltonian zero-mode, normalizable SUSY ground state,
or that any BFSS spectral statement holds.
-/

namespace FCP.BFSSSU2GaugeG4K2B
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open MeasureTheory
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4J FCP.BFSSSU2GaugeG4K1
open FCP.BFSSSU2GaugeG4K2A

/-- The explicit compactly supported radial scalar coefficient.
The pinned Mathlib smooth transition is 1 near 0 and 0 for
arguments ≤ 0. It is evaluated at 2-2*r². -/
noncomputable def radialBumpCoefficient (r : ℝ) : ℂ :=
  (Real.smoothTransition (2 - 2 * r ^ 2) : ℂ)

theorem radialBumpCoefficient_continuous :
    Continuous radialBumpCoefficient := by
  unfold radialBumpCoefficient
  exact Complex.continuous_ofReal.comp
    (Real.smoothTransition.continuous.comp (by fun_prop))

theorem radialBumpCoefficient_zero : radialBumpCoefficient 0 = 1 := by
  simp [radialBumpCoefficient,
    Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2)]

/-- Continuous nonzero fermionic section on the true bosonic
configuration space. -/
theorem radialBumpProfile_continuous :
    Continuous (radialVacuumProfile radialBumpCoefficient) := by
  exact (radialBumpCoefficient_continuous.comp continuous_norm).smul continuous_const

theorem radialBumpProfile_zero_of_large (x : Boson 2) (hx : 1 ≤ ‖x‖) :
    radialVacuumProfile radialBumpCoefficient x = 0 := by
  have hneg : 2 - 2 * ‖x‖ ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg (‖x‖ - 1)]
  simp [radialVacuumProfile, radialBumpCoefficient,
    Real.smoothTransition.zero_of_nonpos hneg]

/-- The true section vanishes outside the unit Euclidean ball,
so it is compactly supported on the genuine finite-dimensional
BFSS Boson 2 configuration space. -/
theorem radialBumpProfile_hasCompactSupport :
    HasCompactSupport (radialVacuumProfile radialBumpCoefficient) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Boson 2) 1)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  exact hx (radialBumpProfile_zero_of_large x (le_of_not_ge hn))

/-- An actual element of upstream BFSS FullL2 2, not a pointwise
function masquerading as an L² state. -/
noncomputable def radialBumpL2 : FullL2 2 :=
  (radialBumpProfile_continuous.memLp_of_hasCompactSupport
    radialBumpProfile_hasCompactSupport
    (p := 2) (μ := (volume : Measure (Boson 2)))).toLp
    (radialVacuumProfile radialBumpCoefficient)

/-- The chosen measurable representative agrees almost everywhere
with the explicitly specified radial vacuum section. -/
theorem radialBumpL2_ae :
    (radialBumpL2 : Boson 2 → Fermion 2) =ᵐ[volume]
      radialVacuumProfile radialBumpCoefficient := by
  exact (radialBumpProfile_continuous.memLp_of_hasCompactSupport
    radialBumpProfile_hasCompactSupport
    (p := 2) (μ := (volume : Measure (Boson 2)))).coeFn_toLp

/-- The nonzero value at the origin becomes a nonzero L²
equivalence class, because the profile is continuous and
Euclidean volume has full support. -/
theorem radialBumpL2_ne_zero : radialBumpL2 ≠ 0 := by
  intro hz
  have hae : (radialVacuumProfile radialBumpCoefficient) =ᵐ[volume]
      (fun _ : Boson 2 => (0 : Fermion 2)) :=
    radialBumpL2_ae.symm.trans
      ((Lp.ext_iff.mp hz).trans
        (Lp.coeFn_zero (E := Fermion 2) (p := 2)
          (μ := (volume : Measure (Boson 2)))))
  have hall : radialVacuumProfile radialBumpCoefficient =
      (fun _ : Boson 2 => (0 : Fermion 2)) :=
    (radialBumpProfile_continuous.ae_eq_iff_eq
      (volume : Measure (Boson 2)) continuous_const).mp hae
  exact (radialVacuumProfile_nonzero_at_origin
    radialBumpCoefficient radialBumpCoefficient_zero) (congrFun hall 0)

/-- The genuine pulled-back L² wavepacket equals the genuine
fermionic fiber action in the PINNED source definitions for every
SU(2) element. This explicitly discharges Gauss invariance. -/
theorem radialBumpL2_pullback_eq_fiberAction (g : GaugeGroup 2) :
    pairedGaugeData.bosonPullback g radialBumpL2 =
      pairedGaugeData.fiberAction g radialBumpL2 := by
  apply Lp.ext_iff.mpr
  have hcomp := Lp.coeFn_compMeasurePreserving radialBumpL2
    (pairedGaugeData.boson g).measurePreserving
  have hfiber := ContinuousLinearMap.coeFn_compLp
    (pairedGaugeData.fermion g).toContinuousLinearEquiv.toContinuousLinearMap
    radialBumpL2
  have hraw := radialBumpL2_ae.comp_tendsto
    (pairedGaugeData.boson g).measurePreserving.quasiMeasurePreserving.tendsto_ae
  filter_upwards [hcomp, hfiber, hraw, radialBumpL2_ae]
      with x hc hf hr hv
  calc
    (pairedGaugeData.bosonPullback g radialBumpL2 : Boson 2 → Fermion 2) x =
        radialBumpL2 (pairedGaugeData.boson g x) := hc
    _ = radialVacuumProfile radialBumpCoefficient
        (pairedGaugeData.boson g x) := hr
    _ = pairedGaugeData.fermion g
        (radialVacuumProfile radialBumpCoefficient x) :=
          pairedGaugeData_radialVacuumProfile_equivariant _ g x
    _ = pairedGaugeData.fermion g (radialBumpL2 x) := by rw [← hv]
    _ = (pairedGaugeData.fiberAction g radialBumpL2 : Boson 2 → Fermion 2) x :=
          hf.symm

/-- A nonzero state actually lies in the exact pinned Gauss physical
Hilbert submodule defined through pullback minus fiber action. -/
theorem radialBumpL2_mem_physicalSpace :
    radialBumpL2 ∈ pairedPhysicalSpace := by
  change radialBumpL2 ∈
    (⨅ g : GaugeGroup 2,
      LinearMap.ker (pairedGaugeData.bosonPullback g -
        pairedGaugeData.fiberAction g))
  rw [Submodule.mem_iInf]
  intro g
  change (pairedGaugeData.bosonPullback g -
    pairedGaugeData.fiberAction g) radialBumpL2 = 0
  exact sub_eq_zero.mpr (radialBumpL2_pullback_eq_fiberAction g)

/-- The true BFSS Gauss physical Hilbert subspace is not bottom.
This is stronger than closedness, vacuum invariance, or pointwise
nonzeroness. -/
theorem pairedPhysicalSpace_ne_bot : pairedPhysicalSpace ≠ ⊥ := by
  intro hbot
  have hmem : radialBumpL2 ∈ pairedPhysicalSpace :=
    radialBumpL2_mem_physicalSpace
  rw [hbot] at hmem
  exact radialBumpL2_ne_zero (by simpa using hmem)

#print axioms radialBumpCoefficient
#print axioms radialBumpCoefficient_continuous
#print axioms radialBumpCoefficient_zero
#print axioms radialBumpProfile_continuous
#print axioms radialBumpProfile_zero_of_large
#print axioms radialBumpProfile_hasCompactSupport
#print axioms radialBumpL2
#print axioms radialBumpL2_ae
#print axioms radialBumpL2_ne_zero
#print axioms radialBumpL2_pullback_eq_fiberAction
#print axioms radialBumpL2_mem_physicalSpace
#print axioms pairedPhysicalSpace_ne_bot

end
end FCP.BFSSSU2GaugeG4K2B
