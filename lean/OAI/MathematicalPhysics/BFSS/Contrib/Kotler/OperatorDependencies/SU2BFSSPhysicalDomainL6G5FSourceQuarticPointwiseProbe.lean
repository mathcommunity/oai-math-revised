import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5EOriginalScalarCoefficientSquareProbe
import OAI.MathematicalPhysics.BFSS.ColorMatrices

/-!
L6G5F: locate the quartic comparison in the unchanged original source.

The bosonic target is the full nine-space commutator-squared expression,
not the separate three-pair deformed potential. The spinor quadratic
source term is reduced to the EXACT pointwise polynomial with original
gammaTwo, structure constants, and ordered position products.

The remaining finite gamma/color contraction is deliberately NOT
asserted here. No gauge, Hamiltonian or spectrum identification.
-/

set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G5F
noncomputable section
open scoped BigOperators
open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G1
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G4A
open FCP.BFSSSU2PhysicalDomainL6G4B
open FCP.BFSSSU2PhysicalDomainL6G5D
open FCP.BFSSSU2PhysicalDomainL6G5E

/-- Bosonic quartic target from the literal source color bracket,
with its original 1/4 factor and all nine ordered spatial pairs. -/
def sourceNineSpatialQuarticPotential {N : ℕ}
    (M : AlgebraData N) (x : Boson N) : ℝ :=
  (1 / 4 : ℝ) * ∑ i : SpaceIndex, ∑ j : SpaceIndex,
    ∑ A : ColorIndex N, (M.coordinateBracketAll x i j A)^2

/-- Independent matrix-commutator meaning of the source bracket target.
This uses the pinned color combination, Hermitian matrix configuration
and upstream coordinate_bracket_norm theorem, no gamma premise. -/
theorem sourceNineSpatialQuarticPotential_matrix {N : ℕ}
    (M : AlgebraData N) (x : Boson N) :
    sourceNineSpatialQuarticPotential M x =
      (1 / 4 : ℝ) * ∑ i : SpaceIndex, ∑ j : SpaceIndex,
        BFSS.hsNormSq
          (BFSS.realBracket (M.matrixConfiguration x i).val
            (M.matrixConfiguration x j).val) := by
  unfold sourceNineSpatialQuarticPotential
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (M.coordinate_bracket_norm x i j).symm

/-- Actual complex pointwise coefficient in L6G5D's *original*
quadratic-position endomorphism, without introducing a new gamma. -/
def sourceQuadraticPointCoefficient {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ)
    (p : FermionLabel N) (x : Boson N) : ℂ :=
  ∑ α : SpinIndex, (w α : ℂ) *
    (∑ v : BosonLabel N, ∑ t : BosonLabel N,
      sourceQuadraticWeight M α p v t *
        ((x v : ℝ) : ℂ) * ((x t : ℝ) : ℂ))

/-- Original position operators multiply pointwise by the original
two coordinates in their original order. -/
private theorem originalPositionPair_apply {N : ℕ}
    (v t : BosonLabel N) (f : SmoothCore N) (x : Boson N) :
    ((sourceP v * sourceP t) f) x =
      (((x v : ℝ) : ℂ) * ((x t : ℝ) : ℂ)) • f x := by
  change (((x v : ℝ) : ℂ) • (((x t : ℝ) : ℂ) • f x)) =
    ((((x v : ℝ) : ℂ) * ((x t : ℝ) : ℂ)) • f x)
  rw [smul_smul]

/-- Actual evaluation of an original core endomorphism at one core test
function and one original bosonic configuration. This is linear because
both the source operator action and SmoothCore evaluation are linear. -/
private def sourceEndPointEvaluation {N : ℕ}
    (f : SmoothCore N) (x : Boson N) :
    SourceEnd N →ₗ[ℂ] Fermion N where
  toFun A := (A f) x
  map_add' A B := by rfl
  map_smul' c A := by rfl

/-- Identifies the L6G5E quadratic operator's pointwise action with
the exact original polynomial coefficient, not a surrogate multiplier. -/
theorem sourceSpinorQuadraticMultiplication_apply {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ)
    (p : FermionLabel N) (f : SmoothCore N) (x : Boson N) :
    (sourceSpinorQuadraticMultiplication M w p f) x =
      (sourceQuadraticPointCoefficient M w p x) • f x := by
  classical
  calc
    (sourceSpinorQuadraticMultiplication M w p f) x =
      ∑ α : SpinIndex, (w α : ℂ) •
        (∑ v : BosonLabel N, ∑ t : BosonLabel N,
          sourceQuadraticWeight M α p v t •
            (((sourceP v * sourceP t) f) x)) := by
              change (sourceEndPointEvaluation f x)
                (sourceSpinorQuadraticMultiplication M w p) = _
              unfold sourceSpinorQuadraticMultiplication
              simp only [map_sum, map_smul]
              rfl
    _ = ∑ α : SpinIndex, (w α : ℂ) •
        (∑ v : BosonLabel N, ∑ t : BosonLabel N,
          (sourceQuadraticWeight M α p v t *
            (((x v : ℝ) : ℂ) * ((x t : ℝ) : ℂ))) • f x) := by
              simp_rw [originalPositionPair_apply, smul_smul]
    _ = _ := by
      unfold sourceQuadraticPointCoefficient
      simp only [Finset.sum_smul, Finset.smul_sum, Finset.mul_sum,
        smul_smul, mul_assoc]

/-- The source quadratic-operator square is precisely multiplication
by the sum of squared original point coefficients on the source core;
the gamma/color quartic contraction remains a separate obligation. -/
theorem sourceSpinorQuadraticSquare_apply {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ)
    (f : SmoothCore N) (x : Boson N) :
    (sourceSpinorQuadraticSquare M w f) x =
      (∑ p : FermionLabel N,
        sourceQuadraticPointCoefficient M w p x *
          sourceQuadraticPointCoefficient M w p x) • f x := by
  classical
  have hterm (p : FermionLabel N) :
      (((sourceSpinorQuadraticMultiplication M w p *
        sourceSpinorQuadraticMultiplication M w p) f) x) =
          (sourceQuadraticPointCoefficient M w p x *
            sourceQuadraticPointCoefficient M w p x) • f x := by
    change (sourceSpinorQuadraticMultiplication M w p
      (sourceSpinorQuadraticMultiplication M w p f)) x = _
    rw [sourceSpinorQuadraticMultiplication_apply]
    rw [sourceSpinorQuadraticMultiplication_apply]
    rw [smul_smul]
  calc
    (sourceSpinorQuadraticSquare M w f) x =
      ∑ p : FermionLabel N,
        (((sourceSpinorQuadraticMultiplication M w p *
          sourceSpinorQuadraticMultiplication M w p) f) x) := by
            change (sourceEndPointEvaluation f x)
              (sourceSpinorQuadraticSquare M w) = _
            unfold sourceSpinorQuadraticSquare
            simp only [map_sum]
            rfl
    _ = ∑ p : FermionLabel N,
        (sourceQuadraticPointCoefficient M w p x *
          sourceQuadraticPointCoefficient M w p x) • f x := by
            apply Finset.sum_congr rfl
            intro p _
            exact hterm p
    _ = _ := by rw [Finset.sum_smul]

#print axioms sourceEndPointEvaluation
#print axioms sourceNineSpatialQuarticPotential_matrix
#print axioms originalPositionPair_apply
#print axioms sourceSpinorQuadraticMultiplication_apply
#print axioms sourceSpinorQuadraticSquare_apply
#check @sourceNineSpatialQuarticPotential_matrix
#check @sourceSpinorQuadraticSquare_apply

end
end FCP.BFSSSU2PhysicalDomainL6G5F
