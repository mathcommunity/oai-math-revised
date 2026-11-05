import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K4ClosedChargeGraphProbe
import OAI.MathematicalPhysics.BFSS.KineticMeasures
import OAI.MathematicalPhysics.BFSS.CovariantFields

/-!
# BFSS SU(2) G4-K5 — actual nonzero physical state's three local energy densities

Gate #133 certifies our concrete nonzero SU(2) physical Hilbert vector
in the *pinned closed BFSS supercharge graph*, with unique charge output.
Gate #132 established that this same state comes from an explicit
nonzero, smooth, compactly supported invariant-core test function.

Here specialize the pinned source's kinetic, bosonic and fermionic
energy density formulas and gauge covariance theorems to THAT
physical core witness. The three actual local densities are proved
continuous, compactly supported, integrable, and invariant for both
genuine SU(2) elements and the entire source-defined unitary-color
boson gauge action. The source kinetic integral identity is recovered
as the sum of squared coordinate derivative L² norms.

This makes honest, finite local-energy quantities available for
future quantitative analysis. There is NO assertion of any energy
minimization, positive spectral gap, energy eigenvector, vanishing
supercharge or physical prediction. This source specialization is
NOT a novel spectral bound.
-/

namespace FCP.BFSSSU2GaugeG4K5
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open MeasureTheory
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2GaugeG4K3
open FCP.BFSSSU2GaugeG4K4

/-- The actual pinned source kinetic density of the verified,
nonzero, compactly supported Gauss-invariant smooth test state. -/
noncomputable def physicalKineticDensity : Boson 2 → ℝ :=
  kineticDensity radialBumpSmoothCore

/-- Exact bosonic and fermionic potential densities at arbitrary
pinned deformation h and mass m, on the very same smooth state. -/
noncomputable def physicalBosonicDensity (h m : ℝ) : Boson 2 → ℝ :=
  pairedAlgebraData.bosonicDensity h m radialBumpSmoothCore

noncomputable def physicalFermionicDensity (h m : ℝ) : Boson 2 → ℝ :=
  pairedAlgebraData.fermionicDensity h m radialBumpSmoothCore

/-- The kinetic density is nonnegative pointwise. -/
theorem physicalKineticDensity_nonneg (x : Boson 2) :
    0 ≤ physicalKineticDensity x :=
  kineticDensity_nonneg radialBumpSmoothCore x

/-- All three literal source-defined densities are continuous. -/
theorem physicalKineticDensity_continuous :
    Continuous physicalKineticDensity :=
  kineticDensity_continuous radialBumpSmoothCore

theorem physicalBosonicDensity_continuous (h m : ℝ) :
    Continuous (physicalBosonicDensity h m) :=
  pairedAlgebraData.bosonicDensity_continuous h m radialBumpSmoothCore

theorem physicalFermionicDensity_continuous (h m : ℝ) :
    Continuous (physicalFermionicDensity h m) :=
  pairedAlgebraData.fermionicDensity_continuous h m radialBumpSmoothCore

/-- Each density is compactly supported in the finite-dimensional
BFSS bosonic configuration space, hence Lebesgue integrable. -/
theorem physicalKineticDensity_compact :
    HasCompactSupport physicalKineticDensity :=
  kineticDensity_compactSupport radialBumpSmoothCore

theorem physicalBosonicDensity_compact (h m : ℝ) :
    HasCompactSupport (physicalBosonicDensity h m) :=
  pairedAlgebraData.bosonicDensity_compactSupport h m radialBumpSmoothCore

theorem physicalFermionicDensity_compact (h m : ℝ) :
    HasCompactSupport (physicalFermionicDensity h m) :=
  pairedAlgebraData.fermionicDensity_compactSupport h m radialBumpSmoothCore

theorem physicalKineticDensity_integrable :
    Integrable physicalKineticDensity (volume : Measure (Boson 2)) :=
  physicalKineticDensity_continuous.integrable_of_hasCompactSupport
    physicalKineticDensity_compact

theorem physicalBosonicDensity_integrable (h m : ℝ) :
    Integrable (physicalBosonicDensity h m) (volume : Measure (Boson 2)) :=
  (physicalBosonicDensity_continuous h m).integrable_of_hasCompactSupport
    (physicalBosonicDensity_compact h m)

theorem physicalFermionicDensity_integrable (h m : ℝ) :
    Integrable (physicalFermionicDensity h m) (volume : Measure (Boson 2)) :=
  (physicalFermionicDensity_continuous h m).integrable_of_hasCompactSupport
    (physicalFermionicDensity_compact h m)

/-- Genuine SU(2) gauge invariance of all three local energy
densities, specialized to the exact G4-K3 invariant-core member. -/
theorem physicalKineticDensity_SU2 (g : GaugeGroup 2) (x : Boson 2) :
    physicalKineticDensity (pairedGaugeData.boson g x) =
      physicalKineticDensity x :=
  pairedGaugeData.invariantCore_kineticDensity radialBumpInvariantCore g x

theorem physicalBosonicDensity_SU2 (h m : ℝ)
    (g : GaugeGroup 2) (x : Boson 2) :
    physicalBosonicDensity h m (pairedGaugeData.boson g x) =
      physicalBosonicDensity h m x :=
  pairedGaugeData.invariantCore_bosonicDensity radialBumpInvariantCore g h m x

theorem physicalFermionicDensity_SU2 (h m : ℝ)
    (g : GaugeGroup 2) (x : Boson 2) :
    physicalFermionicDensity h m (pairedGaugeData.boson g x) =
      physicalFermionicDensity h m x :=
  pairedGaugeData.invariantCore_fermionicDensity radialBumpInvariantCore g h m x

/-- Stronger color-unitary orbit invariance, via the PINNED source
reduction to SU(2) bosonic conjugation (not a substitute action). -/
theorem physicalKineticDensity_unitary
    (U : unitary (ColorMatrix 2)) (x : Boson 2) :
    physicalKineticDensity (pairedAlgebraData.gaugeAction U x) =
      physicalKineticDensity x :=
  pairedGaugeData.invariantCore_kineticDensity_unitary
    (by norm_num : 2 ≤ 2) radialBumpInvariantCore U x

theorem physicalBosonicDensity_unitary (h m : ℝ)
    (U : unitary (ColorMatrix 2)) (x : Boson 2) :
    physicalBosonicDensity h m (pairedAlgebraData.gaugeAction U x) =
      physicalBosonicDensity h m x :=
  pairedGaugeData.invariantCore_bosonicDensity_unitary
    (by norm_num : 2 ≤ 2) radialBumpInvariantCore U h m x

theorem physicalFermionicDensity_unitary (h m : ℝ)
    (U : unitary (ColorMatrix 2)) (x : Boson 2) :
    physicalFermionicDensity h m (pairedAlgebraData.gaugeAction U x) =
      physicalFermionicDensity h m x :=
  pairedGaugeData.invariantCore_fermionicDensity_unitary
    (by norm_num : 2 ≤ 2) radialBumpInvariantCore U h m x

/-- Finite, well-defined real local-energy integral of the three
continuous compactly supported source densities. No sign is
asserted for its fermionic or total components. -/
noncomputable def physicalThreeDensity (h m : ℝ) (x : Boson 2) : ℝ :=
  physicalKineticDensity x +
    physicalBosonicDensity h m x +
      physicalFermionicDensity h m x

theorem physicalThreeDensity_integrable (h m : ℝ) :
    Integrable (physicalThreeDensity h m) (volume : Measure (Boson 2)) :=
  (physicalKineticDensity_integrable.add
    (physicalBosonicDensity_integrable h m)).add
      (physicalFermionicDensity_integrable h m)

theorem physicalThreeDensity_SU2 (h m : ℝ)
    (g : GaugeGroup 2) (x : Boson 2) :
    physicalThreeDensity h m (pairedGaugeData.boson g x) =
      physicalThreeDensity h m x := by
  simp only [physicalThreeDensity, physicalKineticDensity_SU2,
    physicalBosonicDensity_SU2, physicalFermionicDensity_SU2]

/-- The kinetic component's exact Euclidean volume integral
is the PINNED sum of source coordinate-derivative L² norms. -/
theorem physicalKineticDensity_integral_exact :
    (∫ x : Boson 2, physicalKineticDensity x) =
      ∑ p : SpaceIndex × ColorIndex 2,
        ‖coreToL2 (coordinateDerivative p.1 p.2 radialBumpSmoothCore)‖ ^ 2 :=
  kineticDensity_integral radialBumpSmoothCore

#print axioms physicalKineticDensity
#print axioms physicalBosonicDensity
#print axioms physicalFermionicDensity
#print axioms physicalKineticDensity_nonneg
#print axioms physicalKineticDensity_continuous
#print axioms physicalBosonicDensity_continuous
#print axioms physicalFermionicDensity_continuous
#print axioms physicalKineticDensity_compact
#print axioms physicalBosonicDensity_compact
#print axioms physicalFermionicDensity_compact
#print axioms physicalKineticDensity_integrable
#print axioms physicalBosonicDensity_integrable
#print axioms physicalFermionicDensity_integrable
#print axioms physicalKineticDensity_SU2
#print axioms physicalBosonicDensity_SU2
#print axioms physicalFermionicDensity_SU2
#print axioms physicalKineticDensity_unitary
#print axioms physicalBosonicDensity_unitary
#print axioms physicalFermionicDensity_unitary
#print axioms physicalThreeDensity
#print axioms physicalThreeDensity_integrable
#print axioms physicalThreeDensity_SU2
#print axioms physicalKineticDensity_integral_exact

end
end FCP.BFSSSU2GaugeG4K5
