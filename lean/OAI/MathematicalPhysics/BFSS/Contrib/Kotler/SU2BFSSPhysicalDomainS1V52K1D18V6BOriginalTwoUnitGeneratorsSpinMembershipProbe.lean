import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V6AOriginalCliffordStarSignAndEvenPairProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18IOriginalLipschitzGeneratorParityProbe

/-!
K1D18V6B — actual source two-unit Clifford product lies in the
actual pinned Mathlib spinGroup, not merely an abstract orthogonal
matrix or a conditional Spin unit factorization.

The full original S1V0 source quadratic Q and its exact 48-label
vector type remain unchanged. V6A provides both unitary equations
and evenness; the ACCEPTED K1D18I original generator membership in
the genuine lipschitzGroup provides the missing Pin subgroup part.
The pinned SpinGroup.mem_iff then discharges exact Spin membership.

Crucially, neither a single Q=1 Clifford generator nor an arbitrary
Spin element is asserted to admit an even vector factorization.
No full SO48 image surjectivity, covering, global Spin9 or spectral
BFSS consequence is established.

All theorem declarations are candidates until source-pinned strict CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V6B
noncomputable section
open FCP.BFSSS1V0
open CliffordAlgebra

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- An exact ORIGINAL Q-unit vector has an invertible ORIGINAL
Clifford generator. This derives the instance rather than assuming
invertibility for an unrelated surrogate Clifford algebra. -/
theorem source48_unitGenerator_isUnit
    (u : Source48Vector) (hu : Q u = 1) :
    IsUnit (CliffordAlgebra.ι Q u) := by
  have hq : IsUnit (Q u) := by rw [hu]; exact isUnit_one
  exact CliffordAlgebra.isUnit_ι_of_isUnit Q hq

/-- Pair of exactly original Q-unit vectors produces an actual
element of pinned Mathlib's original Spin group. This uses real
unitOfInvertible Clifford units, accepted original Lipschitz
generator membership, actual pair unitary and actual evenness.

Not a generating theorem for arbitrary Spin or surjectivity to SO48. -/
theorem source48_twoUnitGenerators_mem_spin
    (u v : Source48Vector) (hu : Q u = 1) (hv : Q v = 1) :
    CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v ∈ spinGroup Q := by
  have hqu : Q u ≠ 0 := by rw [hu]; exact one_ne_zero
  have hqv : Q v ≠ 0 := by rw [hv]; exact one_ne_zero
  let : Invertible (Q u) := invertibleOfNonzero hqu
  let : Invertible (Q v) := invertibleOfNonzero hqv
  let : Invertible (CliffordAlgebra.ι Q u) :=
    CliffordAlgebra.invertibleιOfInvertible Q u
  let : Invertible (CliffordAlgebra.ι Q v) :=
    CliffordAlgebra.invertibleιOfInvertible Q v
  let x : (CliffordAlgebra Q)ˣ :=
    unitOfInvertible (CliffordAlgebra.ι Q u) *
      unitOfInvertible (CliffordAlgebra.ι Q v)
  have hx : (x : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v := rfl
  have hL : x ∈ lipschitzGroup Q := by
    change unitOfInvertible (CliffordAlgebra.ι Q u) *
      unitOfInvertible (CliffordAlgebra.ι Q v) ∈ lipschitzGroup Q
    exact (lipschitzGroup Q).mul_mem
      (FCP.BFSSS1V52K1D18I.originalSourceGeneratorUnit_mem_lipschitz u)
      (FCP.BFSSS1V52K1D18I.originalSourceGeneratorUnit_mem_lipschitz v)
  have hU : (x : CliffordAlgebra Q) ∈ unitary (CliffordAlgebra Q) := by
    rw [hx]
    exact FCP.BFSSS1V52K1D18V6A.source48_twoUnitGenerators_mem_unitary
      u v hu hv
  have hE : (x : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q := by
    rw [hx]
    exact FCP.BFSSS1V52K1D18V6A.source48_twoGenerators_mem_even u v
  have hS : (x : CliffordAlgebra Q) ∈ spinGroup Q :=
    (spinGroup.mem_iff).2 ⟨(pinGroup.units_mem_iff).2 ⟨hL, hU⟩, hE⟩
  rw [hx] at hS
  exact hS

#print axioms source48_unitGenerator_isUnit
#print axioms source48_twoUnitGenerators_mem_spin

end
end FCP.BFSSS1V52K1D18V6B
