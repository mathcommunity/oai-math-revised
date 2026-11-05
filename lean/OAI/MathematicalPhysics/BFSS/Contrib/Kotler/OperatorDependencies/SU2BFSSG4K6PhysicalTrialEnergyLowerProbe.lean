import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K5ConcreteEnergyDensityProbe
import OAI.MathematicalPhysics.BFSS.ProfileEnergy

/-!
# BFSS SU(2) G4-K6 — a rigorous normalized physical trial-energy lower bound

Using the exact nonzero normalizable SU(2) physical state from Gate #130,
the nonzero invariant smooth-core section from Gate #132,
the pinned source closed supercharge graph from Gate #133, and
the three gauge-invariant, integrable energy densities at Gate #135,
construct the actual deformed BFSS core-energy trial quotient at m=1.

The target is a REAL UNIFORM LOWER ESTIMATE for the explicitly
specified normalized trial state, over 0 < h ≤ 1, obtained by integrating
the pinned ProfileEnergy.coreEnergyDensity_uniform_lower source theorem.
Neither a numerical K nor a positive gap is asserted.

No mass-gap, ground-state, eigenvector, vacuum energy, or empirical
claim is inferred. All definitions refer to the same original pinned
pairedAlgebraData : AlgebraData 2 and genuine SU(2) physical state.
-/

namespace FCP.BFSSSU2GaugeG4K6
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open MeasureTheory
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2GaugeG4K2B
open FCP.BFSSSU2GaugeG4K3
open FCP.BFSSSU2GaugeG4K5

/-- Literal upstream BFSS core-energy density evaluated on the
accepted nonzero smooth Gauss-invariant trial state. The source
contains ONE HALF of the kinetic density, not the full kinetic
density in the diagnostic G4-K5 three-density sum. -/
noncomputable def physicalCoreEnergyDensity (h m : ℝ) : Boson 2 → ℝ :=
  pairedAlgebraData.coreEnergyDensity h m radialBumpSmoothCore

/-- Actual deformed core energy of that same nonzero test state. -/
noncomputable def physicalDeformedEnergy (h m : ℝ) : ℝ :=
  pairedAlgebraData.deformedCoreEnergy h m radialBumpSmoothCore

theorem physicalCoreEnergyDensity_continuous (h m : ℝ) :
    Continuous (physicalCoreEnergyDensity h m) :=
  pairedAlgebraData.coreEnergyDensity_continuous h m radialBumpSmoothCore

theorem physicalCoreEnergyDensity_compact (h m : ℝ) :
    HasCompactSupport (physicalCoreEnergyDensity h m) :=
  pairedAlgebraData.coreEnergyDensity_compactSupport h m radialBumpSmoothCore

theorem physicalCoreEnergyDensity_integrable (h m : ℝ) :
    Integrable (physicalCoreEnergyDensity h m) (volume : Measure (Boson 2)) :=
  (physicalCoreEnergyDensity_continuous h m).integrable_of_hasCompactSupport
    (physicalCoreEnergyDensity_compact h m)

/-- The trial energy is EXACTLY the integral of the pinned
half-kinetic-plus-bosonic-plus-fermionic energy density. -/
theorem physicalCoreEnergyDensity_integral_exact (h m : ℝ) :
    (∫ x : Boson 2, physicalCoreEnergyDensity h m x) =
      physicalDeformedEnergy h m :=
  pairedAlgebraData.coreEnergyDensity_integral h m radialBumpSmoothCore

/-- Exact SU(2) invariance of the FULL source-defined local
core-energy density, with the essential 1/2 kinetic factor. -/
theorem physicalCoreEnergyDensity_SU2 (h m : ℝ)
    (g : GaugeGroup 2) (x : Boson 2) :
    physicalCoreEnergyDensity h m (pairedGaugeData.boson g x) =
      physicalCoreEnergyDensity h m x := by
  change (1 / 2 : ℝ) * physicalKineticDensity (pairedGaugeData.boson g x) +
    (physicalBosonicDensity h m (pairedGaugeData.boson g x) +
      physicalFermionicDensity h m (pairedGaugeData.boson g x)) =
    (1 / 2 : ℝ) * physicalKineticDensity x +
      (physicalBosonicDensity h m x + physicalFermionicDensity h m x)
  rw [physicalKineticDensity_SU2, physicalBosonicDensity_SU2,
    physicalFermionicDensity_SU2]

/-- Integrate the TRUE pinned uniform lower energy-density bound
against Euclidean volume; identify the result via coreToL2_norm_sq
with the exact nonzero G4-K2B physical state.

The universal source constant K need not be sharp, and the
conclusion need not be nonnegative. -/
theorem exists_uniform_physicalEnergy_lower :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ h : ℝ, 0 < h → h ≤ 1 →
        -K * ‖radialBumpL2‖ ^ 2 ≤ physicalDeformedEnergy h 1 := by
  obtain ⟨K, hK, hbound⟩ :=
    pairedAlgebraData.coreEnergyDensity_uniform_lower (by norm_num : 2 ≤ 2)
  refine ⟨K, hK, ?_⟩
  intro h hh hle
  have hpoint (x : Boson 2) :
      -K * ‖radialBumpSmoothCore x‖ ^ 2 ≤ physicalCoreEnergyDensity h 1 x :=
    hbound h hh hle radialBumpSmoothCore x
  have hint :
      (∫ x : Boson 2, -K * ‖radialBumpSmoothCore x‖ ^ 2) ≤
        (∫ x : Boson 2, physicalCoreEnergyDensity h 1 x) :=
    integral_mono
      ((coreNormSq_integrable radialBumpSmoothCore).const_mul (-K))
      (physicalCoreEnergyDensity_integrable h 1) hpoint
  rw [integral_const_mul, ← coreToL2_norm_sq,
    radialBumpSmoothCore_toL2, physicalCoreEnergyDensity_integral_exact] at hint
  exact hint

/-- Genuine normalized BFSS trial-energy quotient of the
nonzero, gauge-invariant L² state. Division is by strictly
positive Hilbert norm squared, not an assumed normalization. -/
noncomputable def physicalNormalizedTrialEnergy (h : ℝ) : ℝ :=
  physicalDeformedEnergy h 1 / ‖radialBumpL2‖ ^ 2

theorem radialBumpL2_norm_sq_pos : 0 < ‖radialBumpL2‖ ^ 2 :=
  pow_pos (norm_pos_iff.mpr radialBumpL2_ne_zero) 2

/-- The actual source-derived lower bound on normalized trial
energy is uniform for 0 < h ≤ 1. This is NOT a spectral gap
or lower bound on every physical state; the single-trial quotient
could be negative. -/
theorem exists_uniform_normalizedTrialEnergy_lower :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ h : ℝ, 0 < h → h ≤ 1 →
        -K ≤ physicalNormalizedTrialEnergy h := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_physicalEnergy_lower
  refine ⟨K, hK, ?_⟩
  intro h hh hle
  change -K ≤ physicalDeformedEnergy h 1 / ‖radialBumpL2‖ ^ 2
  exact (le_div_iff₀ radialBumpL2_norm_sq_pos).mpr
    (hbound h hh hle)

#print axioms physicalCoreEnergyDensity
#print axioms physicalDeformedEnergy
#print axioms physicalCoreEnergyDensity_continuous
#print axioms physicalCoreEnergyDensity_compact
#print axioms physicalCoreEnergyDensity_integrable
#print axioms physicalCoreEnergyDensity_integral_exact
#print axioms physicalCoreEnergyDensity_SU2
#print axioms exists_uniform_physicalEnergy_lower
#print axioms physicalNormalizedTrialEnergy
#print axioms radialBumpL2_norm_sq_pos
#print axioms exists_uniform_normalizedTrialEnergy_lower

end
end FCP.BFSSSU2GaugeG4K6
