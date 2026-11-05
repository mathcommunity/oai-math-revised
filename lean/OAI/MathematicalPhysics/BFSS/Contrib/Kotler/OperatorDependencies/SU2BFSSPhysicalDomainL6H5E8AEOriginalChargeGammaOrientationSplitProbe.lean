import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8ADOppositeGammaOrientationProbe

/-!
# L6H5E8AE — original BFSS supercharge under Clifford-nine orientation reversal

New source-exact PROSPECTIVE proof, not kernel qualified by file creation.

Decompose the literal upstream original AlgebraData.charge into its native
-Complex.I derivative part and 1/2 structure-constant gamma^{ij} position
part on the actual SmoothCore. Replacing gamma_i by -gamma_i negates only
the derivative term: the bivectors and original cubic term stay unchanged.
This will be the operator-algebra side of the full spatial-parity
intertwiner. The latter requires a separate real 27-coordinate inversion
map on TestFunction and FullL2, and remains open.

No manuscript intertwiner, physical graph equality, associated Hamiltonian
domain or spectral assertion is postulated.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 120000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AE
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AD

/-- The exact kinetic (first) summand in pinned AlgebraData.charge. -/
noncomputable def originalKineticPart {N : ℕ}
    (M : AlgebraData N) (α : SpinIndex) :
    SmoothCore N →ₗ[ℂ] SmoothCore N :=
  ∑ i : SpaceIndex, ∑ A : ColorIndex N, ∑ β : SpinIndex,
    (-Complex.I * (M.gamma i α β : ℂ)) •
      ((M.fermionAction β A).comp (coordinateDerivative i A))

/-- The exact cubic-position (second) summand, with original
GammaTwo, color structure constant, and 1/2 normalization. -/
noncomputable def originalCubicPart {N : ℕ}
    (M : AlgebraData N) (α : SpinIndex) :
    SmoothCore N →ₗ[ℂ] SmoothCore N :=
  ∑ i : SpaceIndex, ∑ j : SpaceIndex, ∑ A : ColorIndex N,
    ∑ B : ColorIndex N, ∑ C : ColorIndex N, ∑ β : SpinIndex,
    (((1 / 2 : ℝ) * M.structureConstant A B C * M.gammaTwo i j α β : ℝ) : ℂ) •
      ((M.fermionAction β A).comp ((position i B).comp (position j C)))

/-- No new definition of a charge: this is literally upstream charge. -/
theorem originalCharge_split {N : ℕ} (M : AlgebraData N) (α : SpinIndex) :
    M.charge α = originalKineticPart M α + originalCubicPart M α := rfl

/-- Gamma reversal leaves the actual fermion-action on SmoothCore
unchanged; the paired Fock operators and labeling are identical. -/
theorem oppositeGamma_fermionAction {N : ℕ} (M : AlgebraData N)
    (β : SpinIndex) (A : ColorIndex N) :
    (oppositeGamma M).fermionAction β A = M.fermionAction β A := rfl

/-- Exact source derivative term changes sign under all-nine gamma
reversal; -i, spin order, source coordinateDerivative are unchanged. -/
theorem oppositeGamma_originalKineticPart {N : ℕ}
    (M : AlgebraData N) (α : SpinIndex) :
    originalKineticPart (oppositeGamma M) α = -originalKineticPart M α := by
  classical
  unfold originalKineticPart
  simp only [oppositeGamma_gamma, oppositeGamma_fermionAction]
  simp [Finset.sum_neg_distrib, neg_smul, mul_neg]

/-- Exact full six-index cubic position term is unchanged, including
the original 1/2, structure constants, and gamma bivector matrices. -/
theorem oppositeGamma_originalCubicPart {N : ℕ}
    (M : AlgebraData N) (α : SpinIndex) :
    originalCubicPart (oppositeGamma M) α = originalCubicPart M α := by
  classical
  unfold originalCubicPart
  simp only [oppositeGamma_structureConstant, oppositeGamma_gammaTwo,
    oppositeGamma_fermionAction]

/-- Under gamma reversal the actual source supercharge becomes
minus the original kinetic operator plus the unchanged cubic operator.
This is the exact algebraic side of the proposed parity conjugation. -/
theorem originalCharge_oppositeGamma {N : ℕ}
    (M : AlgebraData N) (α : SpinIndex) :
    (oppositeGamma M).charge α =
      -originalKineticPart M α + originalCubicPart M α := by
  calc
    (oppositeGamma M).charge α =
        originalKineticPart (oppositeGamma M) α +
          originalCubicPart (oppositeGamma M) α :=
      originalCharge_split (oppositeGamma M) α
    _ = -originalKineticPart M α + originalCubicPart M α := by
      rw [oppositeGamma_originalKineticPart, oppositeGamma_originalCubicPart]

#print axioms originalCharge_split
#print axioms oppositeGamma_fermionAction
#print axioms oppositeGamma_originalKineticPart
#print axioms oppositeGamma_originalCubicPart
#print axioms originalCharge_oppositeGamma

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AE
