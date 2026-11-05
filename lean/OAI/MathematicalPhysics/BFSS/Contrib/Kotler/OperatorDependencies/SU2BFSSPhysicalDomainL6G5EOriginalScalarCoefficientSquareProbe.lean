import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5DOriginalCoefficientKineticSplitProbe

/-!
L6G5E — separate the scalar square of the literal source coefficients.

Uses the qualified L6G5D coefficient decomposition and L6G5C
original kinetic square, with no changes to original -i/gammaTwo/1/2
weights, fermion labels, colors or operator order.

Mixed and quadratic-square terms are explicitly named source operators.
They are NOT yet identified with orbital Gauss or quartic potential.
The fermionic CAR response, fermionic Gauss, full Hamiltonian,
gauge restriction and spectrum remain separate obligations.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G5E
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G1
open FCP.BFSSSU2PhysicalDomainL6G2
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G5C
open FCP.BFSSSU2PhysicalDomainL6G5D

/-- Ordered K W + W K, NOT an assumed commuting cross term. -/
def sourceSpinorOrderedMixedTerm {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ) : SourceEnd N :=
  ∑ p : FermionLabel N,
    (sourceSpinorKineticDifferential M w p *
      sourceSpinorQuadraticMultiplication M w p +
     sourceSpinorQuadraticMultiplication M w p *
      sourceSpinorKineticDifferential M w p)

/-- The ordered square of the original quadratic-position component. -/
def sourceSpinorQuadraticSquare {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ) : SourceEnd N :=
  ∑ p : FermionLabel N,
    sourceSpinorQuadraticMultiplication M w p *
      sourceSpinorQuadraticMultiplication M w p

/-- Generic square identity in a NONCOMMUTATIVE ring. -/
private theorem orderedCoefficientSquare_split
    {R I : Type*} [Ring R] [Fintype I] (K W : I → R) :
    (∑ p : I, (K p + W p) * (K p + W p)) =
      (∑ p : I, K p * K p) +
      (∑ p : I, (K p * W p + W p * K p)) +
      (∑ p : I, W p * W p) := by
  calc
    _ = ∑ p : I,
      ((K p * K p + (K p * W p + W p * K p)) + W p * W p) := by
        apply Finset.sum_congr rfl
        intro p _
        noncomm_ring
    _ = _ := by simp only [Finset.sum_add_distrib]

/-- Exact scalar-square split for the literal source coefficient.
This assertion has NO gamma matching premise. -/
theorem sourceAllSpinorCoefficient_rawSquare_split {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ) :
    (∑ p : FermionLabel N,
      sourceAllSpinorCoefficient M w p *
        sourceAllSpinorCoefficient M w p) =
      (∑ p : FermionLabel N,
        sourceSpinorKineticDifferential M w p *
          sourceSpinorKineticDifferential M w p) +
      sourceSpinorOrderedMixedTerm M w +
      sourceSpinorQuadraticSquare M w := by
  classical
  unfold sourceSpinorOrderedMixedTerm sourceSpinorQuadraticSquare
  simp_rw [sourceAllSpinorCoefficient_kinetic_quadratic]
  exact orderedCoefficientSquare_split
    (fun p : FermionLabel N => sourceSpinorKineticDifferential M w p)
    (fun p : FermionLabel N => sourceSpinorQuadraticMultiplication M w p)

/-- Qualified source kinetic Laplacian inserted into the original
CAR-normal-order scalar square. All nonkinetic operators remain explicit.
The gamma equality is visible and was already needed by L6G5C. -/
theorem sourceAllSpinorCoefficient_halfSquare_split {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ)
    (hgamma : M.gamma = originalGamma) :
    (1 / 2 : ℂ) •
      (∑ p : FermionLabel N,
        sourceAllSpinorCoefficient M w p *
          sourceAllSpinorCoefficient M w p) =
      (-(spinorSquareNorm w : ℂ) / 2) •
        sourceOriginalSecondDerivativeSum (N := N) +
      (1 / 2 : ℂ) • sourceSpinorOrderedMixedTerm M w +
      (1 / 2 : ℂ) • sourceSpinorQuadraticSquare M w := by
  rw [sourceAllSpinorCoefficient_rawSquare_split M w]
  rw [smul_add, smul_add]
  rw [sourceSpinorKineticDifferential_halfSquare M w hgamma]

#print axioms orderedCoefficientSquare_split
#print axioms sourceAllSpinorCoefficient_rawSquare_split
#print axioms sourceAllSpinorCoefficient_halfSquare_split
#check @sourceAllSpinorCoefficient_halfSquare_split

end
end FCP.BFSSSU2PhysicalDomainL6G5E
