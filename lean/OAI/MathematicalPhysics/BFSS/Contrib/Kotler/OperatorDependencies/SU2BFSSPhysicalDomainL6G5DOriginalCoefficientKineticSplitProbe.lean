import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5COriginalKineticDifferentialSquareProbe

/-!
L6G5D: identify the accepted kinetic differential with the kinetic
part of the literal sourceAllSpinorCoefficient. The remaining quadratic
operator keeps the source gammaTwo, color constants and 1/2 factor.
No Hamiltonian, Gauss, physical or spectral identity is asserted.
-/

set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G5D
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G4A
open FCP.BFSSSU2PhysicalDomainL6G4B
open FCP.BFSSSU2PhysicalDomainL6G5B
open FCP.BFSSSU2PhysicalDomainL6G5C

private theorem weightedFiniteSum_swap
    {R I J : Type*} [AddCommMonoid R] [Module ℂ R]
    [Fintype I] [Fintype J]
    (w : J → ℂ) (k : J → I → ℂ) (D : I → R) :
    (∑ j : J, w j • (∑ i : I, k j i • D i)) =
      ∑ i : I, (∑ j : J, w j * k j i) • D i := by
  calc
    _ = ∑ j : J, ∑ i : I, (w j * k j i) • D i := by
      simp only [Finset.smul_sum, smul_smul]
    _ = ∑ i : I, ∑ j : J, (w j * k j i) • D i := Finset.sum_comm
    _ = _ := by simp only [Finset.sum_smul]

def sourceSpinorQuadraticMultiplication {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ)
    (p : FermionLabel N) : SourceEnd N :=
  ∑ α : SpinIndex, (w α : ℂ) •
    (∑ v : BosonLabel N, ∑ t : BosonLabel N,
      sourceQuadraticWeight M α p v t • (sourceP v * sourceP t))

/-- Original source coefficient equals exact kinetic plus quadratic. -/
theorem sourceAllSpinorCoefficient_kinetic_quadratic {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ)
    (p : FermionLabel N) :
    sourceAllSpinorCoefficient M w p =
      sourceSpinorKineticDifferential M w p +
        sourceSpinorQuadraticMultiplication M w p := by
  classical
  have hkin :
      (∑ α : SpinIndex, (w α : ℂ) •
        (∑ u : BosonLabel N,
          sourceKineticWeight M α p u • sourceD u)) =
        sourceSpinorKineticDifferential M w p := by
    unfold sourceSpinorKineticDifferential sourceSpinorKineticWeight
    exact weightedFiniteSum_swap
      (fun α : SpinIndex => (w α : ℂ))
      (fun α : SpinIndex => sourceKineticWeight M α p)
      (sourceD (N := N))
  calc
    sourceAllSpinorCoefficient M w p =
      (∑ α : SpinIndex, (w α : ℂ) •
        (∑ u : BosonLabel N,
          sourceKineticWeight M α p u • sourceD u)) +
        sourceSpinorQuadraticMultiplication M w p := by
        unfold sourceAllSpinorCoefficient sourceSpinorQuadraticMultiplication
        simp_rw [sourceCoefficient_eq_polynomial]
        unfold differentialPolynomial
        simp only [smul_add, Finset.sum_add_distrib]
    _ = _ := by rw [hkin]

#print axioms weightedFiniteSum_swap
#print axioms sourceAllSpinorCoefficient_kinetic_quadratic
#check @sourceAllSpinorCoefficient_kinetic_quadratic

end
end FCP.BFSSSU2PhysicalDomainL6G5D
