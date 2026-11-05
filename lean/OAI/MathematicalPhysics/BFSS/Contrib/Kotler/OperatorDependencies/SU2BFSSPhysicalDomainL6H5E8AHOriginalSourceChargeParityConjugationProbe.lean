import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AEOriginalChargeGammaOrientationSplitProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AGOriginalSmoothParityDerivativeProbe

/-!
# H5E8AH — Full source supercharge under genuine smooth-core parity

Prospective **exact original source** supercharge-parity theorem.
Only uses qualified source AD/AE/AF/AG; no new source gamma,
Clifford, Hilbert-space or physical-domain axiom.

To avoid unfolding an enormous sixfold original source charge during
elaboration, build parity conjugation as a linear map on the algebra of
smooth-core endomorphisms. Prove its multiplicativity using P²=1.
Transport each original fermion/derivative and fermion/position/position
monomial once, then use map_sum on original source finite sums.

The exact SmoothCore identity is **not** a FullL2 unitary/physical
graph/Hamiltonian-domain equality or manuscript Spin(48) equivalence.
Unqualified until strict source-pinned axiom-audited CI passes.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 120000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AH
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AD
open FCP.BFSSSU2PhysicalDomainL6H5E8AE
open FCP.BFSSSU2PhysicalDomainL6H5E8AF
open FCP.BFSSSU2PhysicalDomainL6H5E8AG

private abbrev CoreEnd (N : ℕ) := SmoothCore N →ₗ[ℂ] SmoothCore N

private theorem parity_twice_apply {N : ℕ} (f : SmoothCore N) :
    originalSmoothParity (originalSmoothParity f) = f := by
  have h := congrArg (fun T : CoreEnd N => T f)
    (originalSmoothParity_involutive (N := N))
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h

/-- Conjugation by the accepted actual spatial inversion on SmoothCore.
It is complex-linear as an operator on complex-linear core endomorphisms. -/
noncomputable def parityConjugation {N : ℕ} :
    CoreEnd N →ₗ[ℂ] CoreEnd N where
  toFun := fun T =>
    (originalSmoothParity (N := N)).comp (T.comp originalSmoothParity)
  map_add' T U := by
    apply LinearMap.ext
    intro f
    simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
  map_smul' c T := by
    apply LinearMap.ext
    intro f
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul,
      RingHom.id_apply]

/-- Literal composition preservation, using actual source P²=1. -/
theorem parityConjugation_comp {N : ℕ} (T U : CoreEnd N) :
    parityConjugation (T.comp U) =
      (parityConjugation T).comp (parityConjugation U) := by
  apply LinearMap.ext
  intro f
  change
    originalSmoothParity (T (U (originalSmoothParity f))) =
    originalSmoothParity (T
      (originalSmoothParity (originalSmoothParity
        (U (originalSmoothParity f)))))
  rw [parity_twice_apply]

private theorem parityConjugation_of_anticommute {N : ℕ}
    (T : CoreEnd N)
    (h : (originalSmoothParity (N := N)).comp T =
      -(T.comp originalSmoothParity)) :
    parityConjugation T = -T := by
  apply LinearMap.ext
  intro f
  have hv := congrArg (fun R : CoreEnd N => R (originalSmoothParity f)) h
  change originalSmoothParity (T (originalSmoothParity f)) =
    -(T (originalSmoothParity (originalSmoothParity f))) at hv
  -- Unfold the bundled conjugation map at this specific test vector;
  -- the original pointwise operator equality is exactly hv.
  change originalSmoothParity (T (originalSmoothParity f)) = -(T f)
  simpa only [parity_twice_apply] using hv

private theorem parityConjugation_of_commute {N : ℕ}
    (T : CoreEnd N)
    (h : (originalSmoothParity (N := N)).comp T =
      T.comp originalSmoothParity) :
    parityConjugation T = T := by
  apply LinearMap.ext
  intro f
  have hv := congrArg (fun R : CoreEnd N => R (originalSmoothParity f)) h
  change originalSmoothParity (T (originalSmoothParity f)) =
    T (originalSmoothParity (originalSmoothParity f)) at hv
  change originalSmoothParity (T (originalSmoothParity f)) = T f
  simpa only [parity_twice_apply] using hv

/-- Exact original fermion action is even under spatial inversion. -/
theorem parityConjugation_fermionAction {N : ℕ}
    (M : AlgebraData N) (β : SpinIndex) (A : ColorIndex N) :
    parityConjugation (M.fermionAction β A) = M.fermionAction β A :=
  parityConjugation_of_commute _ (originalSmoothParity_fermionAction M β A)

/-- Each exact original first-order coordinate derivative is odd. -/
theorem parityConjugation_coordinateDerivative {N : ℕ}
    (i : SpaceIndex) (A : ColorIndex N) :
    parityConjugation (coordinateDerivative i A) =
      -(coordinateDerivative i A) :=
  parityConjugation_of_anticommute _
    (originalSmoothParity_coordinateDerivative i A)

/-- Each exact original color-resolved position multiplier is odd. -/
theorem parityConjugation_position {N : ℕ}
    (i : SpaceIndex) (A : ColorIndex N) :
    parityConjugation (position i A) = -(position i A) :=
  parityConjugation_of_anticommute _
    (originalSmoothParity_position i A)

/-- The literal original first-order monomial has odd parity.
The fermion operator acts after the actual source coordinate derivative. -/
theorem parityConjugation_fermionDerivative {N : ℕ}
    (M : AlgebraData N) (β : SpinIndex)
    (i : SpaceIndex) (A : ColorIndex N) :
    parityConjugation ((M.fermionAction β A).comp
      (coordinateDerivative i A)) =
      -((M.fermionAction β A).comp (coordinateDerivative i A)) := by
  rw [parityConjugation_comp, parityConjugation_fermionAction,
    parityConjugation_coordinateDerivative]
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, map_neg]

/-- Two real position multipliers are even under genuine source parity. -/
theorem parityConjugation_positionPair {N : ℕ}
    (i j : SpaceIndex) (B C : ColorIndex N) :
    parityConjugation ((position i B).comp (position j C)) =
      (position i B).comp (position j C) := by
  rw [parityConjugation_comp, parityConjugation_position,
    parityConjugation_position]
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, map_neg, neg_neg]

/-- An exact source six-index cubic monomial is parity-even. -/
theorem parityConjugation_fermionPositionPair {N : ℕ}
    (M : AlgebraData N) (β : SpinIndex)
    (A B C : ColorIndex N) (i j : SpaceIndex) :
    parityConjugation
      ((M.fermionAction β A).comp ((position i B).comp (position j C))) =
      (M.fermionAction β A).comp ((position i B).comp (position j C)) := by
  rw [parityConjugation_comp, parityConjugation_fermionAction,
    parityConjugation_positionPair]

/-- The true original nine-space/three-color/sixteen-spin kinetic charge
is odd under conjugation by source spatial inversion. -/
theorem parityConjugation_originalKineticPart {N : ℕ}
    (M : AlgebraData N) (α : SpinIndex) :
    parityConjugation (originalKineticPart M α) =
      -originalKineticPart M α := by
  unfold originalKineticPart
  simp only [map_sum, map_smul, parityConjugation_fermionDerivative]
  simp [Finset.sum_neg_distrib]

/-- The true original six-index cubic source charge is parity-even. -/
theorem parityConjugation_originalCubicPart {N : ℕ}
    (M : AlgebraData N) (α : SpinIndex) :
    parityConjugation (originalCubicPart M α) =
      originalCubicPart M α := by
  unfold originalCubicPart
  simp only [map_sum, map_smul, parityConjugation_fermionPositionPair]

/-- Exact full original source supercharge is conjugate, on the *actual
source SmoothCore N*, to the opposite Clifford-nine gamma orientation.
The source gamma, -i, 1/2, all finite sums and fermion mode labels
are unchanged. No statement about the closed physical graph yet. -/
theorem originalCharge_parityConjugate {N : ℕ}
    (M : AlgebraData N) (α : SpinIndex) :
    (oppositeGamma M).charge α =
      (originalSmoothParity (N := N)).comp
        ((M.charge α).comp (originalSmoothParity (N := N))) := by
  change (oppositeGamma M).charge α = parityConjugation (M.charge α)
  calc
    (oppositeGamma M).charge α =
        -originalKineticPart M α + originalCubicPart M α :=
      originalCharge_oppositeGamma M α
    _ = parityConjugation
          (originalKineticPart M α + originalCubicPart M α) := by
      rw [map_add, parityConjugation_originalKineticPart,
        parityConjugation_originalCubicPart]
    _ = parityConjugation (M.charge α) := by
      rw [originalCharge_split]

#print axioms parityConjugation
#print axioms parityConjugation_comp
#print axioms parityConjugation_fermionDerivative
#print axioms parityConjugation_fermionPositionPair
#print axioms parityConjugation_originalKineticPart
#print axioms parityConjugation_originalCubicPart
#print axioms originalCharge_parityConjugate

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AH
