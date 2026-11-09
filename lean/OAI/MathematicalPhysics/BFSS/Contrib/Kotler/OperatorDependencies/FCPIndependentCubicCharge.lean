import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentPosition

/-!
M4E4B — genuinely independently defined cubic BFSS supercharge component.

The input color basis gives its own real structure constants through
the -i commutator and trace, and the input real gamma matrices give
their own antisymmetric gammaTwo coefficients. The cubic sum uses
exactly (1/2) * f_ABC * gamma^{ij}_{αβ}, the original index order,
and independent Majorana action AFTER position i B AFTER position j C.

The entire cubic definition is independent of J and source Fock
operators. Source equality is separately proved under exact
color/gamma and 48-Majorana intertwining hypotheses.

This theorem will not establish all 16 supercharges, the closed
charge graph, the Hamiltonian or any spectral result.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.IndependentSmoothSupercharge
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.IndependentSmoothCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

/-- Direct independent Lie-color bracket with the original -i sign. -/
def independentColorBracket
    (x y : ColorMatrix 2) : ColorMatrix 2 :=
  (-Complex.I) • (x * y - y * x)

/-- Independent real f_ABC from the color basis, -i bracket and trace. -/
def independentStructureConstant
    (color : ColorIndex 2 → ColorMatrix 2)
    (A B C : ColorIndex 2) : ℝ :=
  (Matrix.trace (color A *
    independentColorBracket (color B) (color C))).re

/-- Independent antisymmetrized 16x16 gamma matrix, 1/2 commutator. -/
def independentGammaTwo
    (gamma : SpaceIndex → GammaMatrix)
    (i j : SpaceIndex) : GammaMatrix :=
  (1 / 2 : ℝ) • (gamma i * gamma j - gamma j * gamma i)

/-- Explicit color input identifies independent f_ABC with the literal
source AlgebraData.structureConstant, not an assumed coefficient. -/
theorem independentStructureConstant_source
    (A B C : ColorIndex 2) :
    independentStructureConstant pairedAlgebraData.color A B C =
      pairedAlgebraData.structureConstant A B C := by
  rfl

/-- Explicit real gamma input identifies the independent commutator
with the literal source AlgebraData.gammaTwo. -/
theorem independentGammaTwo_source (i j : SpaceIndex) :
    independentGammaTwo pairedAlgebraData.gamma i j =
      pairedAlgebraData.gammaTwo i j := by
  rfl

/-- Independent E-valued cubic multiplication operator. Exact source
coefficient and source operator ORDER are preserved in the definition:
theta β A ∘ position i B ∘ position j C. -/
def independentCubicCharge
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (α : SpinIndex) :
    IndependentTestCore E →ₗ[ℂ] IndependentTestCore E :=
  ∑ i : SpaceIndex, ∑ j : SpaceIndex, ∑ A : ColorIndex 2,
    ∑ B : ColorIndex 2, ∑ C : ColorIndex 2, ∑ β : SpinIndex,
    (((1 / 2 : ℝ) * independentStructureConstant color A B C *
      independentGammaTwo gamma i j α β : ℝ) : ℂ) •
      ((independentFermionCoreAction theta β A).comp
        ((independentPosition i B).comp (independentPosition j C)))

/-- Exact original source cubic-charge summand identified term-by-term,
using both genuine independent tensor definitions and operator actions.
No transported cubic operator or extra hypothesis on the E-core is used. -/
theorem independentCubicCharge_intertwining
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (α : SpinIndex) (f : IndependentTestCore E) :
    independentSmoothTransport J (independentCubicCharge color gamma theta α f) =
      (∑ i : SpaceIndex, ∑ j : SpaceIndex, ∑ A : ColorIndex 2,
        ∑ B : ColorIndex 2, ∑ C : ColorIndex 2, ∑ β : SpinIndex,
        (((1 / 2 : ℝ) * pairedAlgebraData.structureConstant A B C *
          pairedAlgebraData.gammaTwo i j α β : ℝ) : ℂ) •
          ((pairedAlgebraData.fermionAction β A).comp
            ((position i B).comp (position j C))))
        (independentSmoothTransport J f) := by
  subst color
  subst gamma
  have hterm (i j : SpaceIndex)
      (A B C : ColorIndex 2) (β : SpinIndex) :
      independentSmoothTransport J
        (independentFermionCoreAction theta β A
          (independentPosition i B (independentPosition j C f))) =
      pairedAlgebraData.fermionAction β A
        (position i B (position j C (independentSmoothTransport J f))) := by
    rw [independentFermionCoreAction_intertwining theta J hJ β A
      (independentPosition i B (independentPosition j C f))]
    rw [independentPosition_intertwining J i B (independentPosition j C f)]
    rw [independentPosition_intertwining J j C f]
  simp only [independentCubicCharge,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    map_sum, map_smul]
  simp_rw [independentStructureConstant_source, independentGammaTwo_source, hterm]

#print axioms independentColorBracket
#print axioms independentStructureConstant
#print axioms independentGammaTwo
#print axioms independentStructureConstant_source
#print axioms independentGammaTwo_source
#print axioms independentCubicCharge
#print axioms independentCubicCharge_intertwining

end
end FCP.IndependentSmoothSupercharge
