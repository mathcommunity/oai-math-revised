import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5OOriginalComplexQuarticOperatorProbe

/-!
L6G5P — after the qualified original quartic potential, identify the
EXACT residual mixed kinetic/quadratic operator in the original scalar
coefficient square. Preserve both orders KW and WK; isolate a
right-ordered first-derivative term and a true source commutator.

The decomposition is source-exact but the residual is NOT assumed
to equal orbital Gauss. The fermionic CAR response/Gauss remain
separate, as do gauge restriction and physical spectrum.
-/
set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G5P
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G1
open FCP.BFSSSU2PhysicalDomainL6G2
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G5C
open FCP.BFSSSU2PhysicalDomainL6G5D
open FCP.BFSSSU2PhysicalDomainL6G5E
open FCP.BFSSSU2PhysicalDomainL6G5F
open FCP.BFSSSU2PhysicalDomainL6G5O

/-- Genuine first-order candidate in a fixed RIGHT ordering: W K.
No false commutation of a differential operator with position. -/
def sourceSpinorRightOrderedMixed {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ) : SourceEnd N :=
  ∑ p : FermionLabel N,
    sourceSpinorQuadraticMultiplication M w p *
      sourceSpinorKineticDifferential M w p

/-- Exact summed commutator of ORIGINAL differential K and original
quadratic-position W; its evaluation still needs the derivative-of-W
and actual orbital-Gauss identification. -/
def sourceSpinorMixedCommutator {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ) : SourceEnd N :=
  ∑ p : FermionLabel N,
    (sourceSpinorKineticDifferential M w p *
      sourceSpinorQuadraticMultiplication M w p -
     sourceSpinorQuadraticMultiplication M w p *
      sourceSpinorKineticDifferential M w p)

/-- Purely noncommutative finite algebra. Only the scalar TWO is
distributed; no assumption that K and W commute. -/
private theorem orderedMixed_firstOrder_commutator
    {R I : Type*} [Ring R] [Algebra ℂ R] [Fintype I]
    (K W : I → R) :
    (∑ p : I, (K p * W p + W p * K p)) =
      (2 : ℂ) • (∑ p : I, W p * K p) +
        (∑ p : I, (K p * W p - W p * K p)) := by
  classical
  calc
    _ = ∑ p : I,
        ((2 : ℂ) • (W p * K p) +
          (K p * W p - W p * K p)) := by
            apply Finset.sum_congr rfl
            intro p _
            have htwo : (2 : ℂ) • (W p * K p) =
                (W p * K p) + (W p * K p) := by
              rw [show (2 : ℂ) = (1 : ℂ) + 1 by norm_num,
                add_smul, one_smul]
            rw [htwo]
            noncomm_ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.smul_sum]

/-- Source-specific ordered mixed component is two genuinely
right-ordered WK terms PLUS the true KW-WK commutator response. -/
theorem sourceSpinorOrderedMixedTerm_split {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ) :
    sourceSpinorOrderedMixedTerm M w =
      (2 : ℂ) • sourceSpinorRightOrderedMixed M w +
        sourceSpinorMixedCommutator M w := by
  classical
  unfold sourceSpinorOrderedMixedTerm sourceSpinorRightOrderedMixed
    sourceSpinorMixedCommutator
  exact orderedMixed_firstOrder_commutator
    (fun p : FermionLabel N => sourceSpinorKineticDifferential M w p)
    (fun p : FermionLabel N => sourceSpinorQuadraticMultiplication M w p)

/-- Source scalar coefficient square on every original SmoothCore test
function after inserting the fully qualified kinetic and quartic
potential terms. The ordered mixed differential term is still explicit.
This is NOT a full supercharge-square/Hamiltonian-Gauss identity. -/
theorem sourceSU2HalfScalarSquare_kinetic_mixed_potential_apply
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (w : SpinIndex → ℝ)
    (hgamma : M.gamma = originalGamma)
    (f : SmoothCore 2) (x : Boson 2) :
    (((1 / 2 : ℂ) •
      (∑ p : FermionLabel 2,
        sourceAllSpinorCoefficient M w p *
          sourceAllSpinorCoefficient M w p)) f) x =
      (((-(spinorSquareNorm w : ℂ) / 2) •
          sourceOriginalSecondDerivativeSum (N := 2) +
        (1 / 2 : ℂ) • sourceSpinorOrderedMixedTerm M w) f) x +
      ((spinorSquareNorm w : ℂ) *
        (sourceNineSpatialQuarticPotential M x : ℂ)) • f x := by
  rw [sourceAllSpinorCoefficient_halfSquare_split M w hgamma]
  change
    (((-(spinorSquareNorm w : ℂ) / 2) •
          sourceOriginalSecondDerivativeSum (N := 2) +
        (1 / 2 : ℂ) • sourceSpinorOrderedMixedTerm M w) f) x +
      (((1 / 2 : ℂ) • sourceSpinorQuadraticSquare M w) f) x = _
  rw [sourceSU2QuadraticSquare_potential_apply M hcolor w f x]

#print axioms orderedMixed_firstOrder_commutator
#print axioms sourceSpinorOrderedMixedTerm_split
#print axioms sourceSU2HalfScalarSquare_kinetic_mixed_potential_apply
#check @sourceSU2HalfScalarSquare_kinetic_mixed_potential_apply
end
end FCP.BFSSSU2PhysicalDomainL6G5P
