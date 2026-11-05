import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V6BOriginalTwoUnitGeneratorsSpinMembershipProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18EOriginalSpinTwoFactorDeterminantProbe

/-!
K1D18V6C — construct the ACTUAL original Spin group element
represented by a product of two exact unit-Q source Clifford
generators, then discharge the source-exact K1D18D/E conditional
two-unit factorization antecedent for THIS constructed element.

No statement that every Spin element factors this way, no proof
that all special orthogonal transformations lie in the image,
and no topological covering, global Spin9 or BFSS spectral claim.
CANDIDATE pending fresh source-pinned strict CI and axiom audit.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V6C
noncomputable section
open FCP.BFSSS1V0
open Matrix
open CliffordAlgebra

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- A concrete genuine original Mathlib Spin element with no
surrogate group: use V6B's accepted membership proof. -/
noncomputable def originalSourceUnitPairSpin
    (u v : Source48Vector) (hu : Q u = 1) (hv : Q v = 1) :
    spinGroup Q :=
  ⟨CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v,
    FCP.BFSSS1V52K1D18V6B.source48_twoUnitGenerators_mem_spin u v hu hv⟩

/-- The *actual* Spin-to-Clifford-units map of our constructed
source pair is the product of the corresponding actual Clifford
generator units, precisely discharging K1D18D/E factorization. -/
theorem originalSourceUnitPairSpin_toUnits
    (u v : Source48Vector) (hu : Q u = 1) (hv : Q v = 1)
    [Invertible (CliffordAlgebra.ι Q u)]
    [Invertible (CliffordAlgebra.ι Q v)] :
    spinGroup.toUnits (originalSourceUnitPairSpin u v hu hv) =
      unitOfInvertible (CliffordAlgebra.ι Q u) *
        unitOfInvertible (CliffordAlgebra.ι Q v) := by
  apply Units.ext
  rfl

/-- The original real-vector Spin action on the constructed genuine
Spin pair is EXACTLY the product of the two accepted source-rank-one
Clifford conjugation matrices, in the original label basis. -/
theorem originalSourceUnitPairSpin_action
    (u v w : Source48Vector) (hu : Q u = 1) (hv : Q v = 1)
    [Invertible (Q u)] [Invertible (Q v)] :
    FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry
      (originalSourceUnitPairSpin u v hu hv) w =
      FCP.BFSSS1V37.source48_rankOneConjugationMatrix u
        (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow u) *ᵥ
      (FCP.BFSSS1V37.source48_rankOneConjugationMatrix v
        (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow v) *ᵥ w) := by
  let : Invertible (CliffordAlgebra.ι Q u) :=
    CliffordAlgebra.invertibleιOfInvertible Q u
  let : Invertible (CliffordAlgebra.ι Q v) :=
    CliffordAlgebra.invertibleιOfInvertible Q v
  exact FCP.BFSSS1V52K1D18D.originalSourceSpin48Isometry_twoGeneratorMatrices_of_unitFactorization
    (originalSourceUnitPairSpin u v hu hv) u v w
      (originalSourceUnitPairSpin_toUnits u v hu hv)

/-- The GENUINE original Spin real-linear action attached to this
constructed pair has determinant +1. This is a resolved example,
not universal SO48 surjectivity nor arbitrary Spin factorization. -/
theorem originalSourceUnitPairSpin_linearMap_det_one
    (u v : Source48Vector) (hu : Q u = 1) (hv : Q v = 1) :
    LinearMap.det
      (FCP.BFSSS1V52K1D13.originalSourceSpin48LinearMap
        (originalSourceUnitPairSpin u v hu hv)) = (1 : ℝ) := by
  have hqu : Q u ≠ 0 := by rw [hu]; exact one_ne_zero
  have hqv : Q v ≠ 0 := by rw [hv]; exact one_ne_zero
  let : Invertible (Q u) := invertibleOfNonzero hqu
  let : Invertible (Q v) := invertibleOfNonzero hqv
  let : Invertible (CliffordAlgebra.ι Q u) :=
    CliffordAlgebra.invertibleιOfInvertible Q u
  let : Invertible (CliffordAlgebra.ι Q v) :=
    CliffordAlgebra.invertibleιOfInvertible Q v
  exact FCP.BFSSS1V52K1D18E.originalSourceSpin48LinearMap_det_one_of_twoUnitFactorization
    (originalSourceUnitPairSpin u v hu hv) u v
      (originalSourceUnitPairSpin_toUnits u v hu hv)

#print axioms originalSourceUnitPairSpin
#print axioms originalSourceUnitPairSpin_toUnits
#print axioms originalSourceUnitPairSpin_action
#print axioms originalSourceUnitPairSpin_linearMap_det_one

end
end FCP.BFSSS1V52K1D18V6C
