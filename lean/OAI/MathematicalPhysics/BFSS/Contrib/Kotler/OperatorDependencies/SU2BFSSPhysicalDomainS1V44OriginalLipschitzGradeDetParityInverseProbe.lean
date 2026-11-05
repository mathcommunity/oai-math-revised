import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V43OriginalLipschitzGradeDetParityInterfacesProbe
import Mathlib.Algebra.Group.Units.Hom

/-!
S1V44 — TRUE source Lipschitz grade/determinant parity under inverse.
Exact source original Q, Clifford involute, actual determinant character,
actual Lipschitz subgroup, immutable etblink/math and pinned Lean/Mathlib.

Separate the proof from concretely expanded Fock or Clifford expressions:
lift involute and scalar algebra maps through Units.map and use invertible
unit-group equality. Four bounded roots, no universal closure or Spin theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V44
noncomputable section

open FCP.BFSSS1V0
private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev A := CliffordAlgebra Q
private abbrev δ := FCP.BFSSS1V41.sourceLipschitz48OriginalRealDetCharacter

/-- The actual pinned Clifford grade-involution lifted to true units. -/
noncomputable def source48GradeOnUnits : Aˣ →* Aˣ :=
  Units.map (CliffordAlgebra.involute (Q := Q)).toRingHom.toMonoidHom

/-- The central REAL scalar embedding lifted to Clifford units. -/
noncomputable def source48RealScalarOnUnits : ℝˣ →* Aˣ :=
  Units.map (algebraMap ℝ A).toMonoidHom

/-- Every actual invertible scalar unit commutes with every Clifford unit. -/
theorem source48RealScalarOnUnits_commutes (d : ℝˣ) (u : Aˣ) :
    source48RealScalarOnUnits d * u = u * source48RealScalarOnUnits d := by
  apply Units.ext
  change algebraMap ℝ A (d : ℝ) * (u : A) =
    (u : A) * algebraMap ℝ A (d : ℝ)
  exact Algebra.commutes (d : ℝ) (u : A)

/-- The original S1V43 grade/determinant relation is equivalent to a
genuine equality in the ACTUAL Clifford unit group. -/
theorem source48LipschitzGradeDetParity_iff_units (x : lipschitzGroup Q) :
    FCP.BFSSS1V43.source48LipschitzGradeDetParity x ↔
      source48GradeOnUnits (x : Aˣ) =
        source48RealScalarOnUnits (δ x) * (x : Aˣ) := by
  constructor
  · intro hx
    apply Units.ext
    change CliffordAlgebra.involute (((x : Aˣ) : A)) =
      algebraMap ℝ A ((δ x : ℝ)) * (((x : Aˣ) : A))
    simpa only [FCP.BFSSS1V43.source48LipschitzGradeDetParity,
      Algebra.smul_def] using hx
  · intro hx
    have hh := congrArg (fun u : Aˣ => (u : A)) hx
    change CliffordAlgebra.involute (((x : Aˣ) : A)) =
      algebraMap ℝ A ((δ x : ℝ)) * (((x : Aˣ) : A)) at hh
    change CliffordAlgebra.involute (((x : Aˣ) : A)) =
      (δ x : ℝ) • (((x : Aˣ) : A))
    simpa only [Algebra.smul_def] using hh

/-- The actual grade-involute / true source Lipschitz determinant relation
holds under the inverse of an ARBITRARY genuine Lipschitz element on which
it already holds. This does NOT assert that it holds on all such elements. -/
theorem source48LipschitzGradeDetParity_inv
    (x : lipschitzGroup Q)
    (hx : FCP.BFSSS1V43.source48LipschitzGradeDetParity x) :
    FCP.BFSSS1V43.source48LipschitzGradeDetParity x⁻¹ := by
  apply (source48LipschitzGradeDetParity_iff_units x⁻¹).2
  have heq := (source48LipschitzGradeDetParity_iff_units x).1 hx
  calc
    source48GradeOnUnits ((x⁻¹ : lipschitzGroup Q) : Aˣ) =
        (source48GradeOnUnits (x : Aˣ))⁻¹ := by
      rw [show ((x⁻¹ : lipschitzGroup Q) : Aˣ) = (x : Aˣ)⁻¹ from rfl]
      exact map_inv source48GradeOnUnits _
    _ = (source48RealScalarOnUnits (δ x) * (x : Aˣ))⁻¹ := by rw [heq]
    _ = (x : Aˣ)⁻¹ * (source48RealScalarOnUnits (δ x))⁻¹ :=
      mul_inv_rev _ _
    _ = source48RealScalarOnUnits (δ x⁻¹) *
          ((x⁻¹ : lipschitzGroup Q) : Aˣ) := by
      simpa only [map_inv, Subgroup.coe_inv] using
        (source48RealScalarOnUnits_commutes ((δ x)⁻¹) ((x : Aˣ)⁻¹)).symm

#print axioms source48GradeOnUnits
#print axioms source48RealScalarOnUnits
#print axioms source48RealScalarOnUnits_commutes
#print axioms source48LipschitzGradeDetParity_iff_units
#print axioms source48LipschitzGradeDetParity_inv

end
end FCP.BFSSS1V44
