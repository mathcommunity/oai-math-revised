import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V41GenuineLipschitz48RealGLHomProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V39Original48CliffordGeneratorMatrixActionProbe
import Mathlib.LinearAlgebra.Determinant

/-!
S1V42 — genuine ORIGINAL Clifford unit generator in the ACTUAL source
Lipschitz subgroup, exact action as the S1V39 original rank-one
48-real matrix, and determinant -1 in the actual S1V41 character.

The source Q, 48 original coordinate labels, Clifford conventions,
and actual Lipschitz subgroup are unchanged. No assumed Pin group,
no arbitrary factorization of Spin, no parity induction, global SU2
lift, manuscript representation or spectral conclusion.

The four roots are UNACCEPTED until exact pinned strict CI qualification.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V42
noncomputable section

open Matrix
open FCP.BFSSS1V0
open FCP.BFSSS1V40

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- A real source vector with invertible ORIGINAL Q defines the
GENUINE unit of the pinned original Clifford algebra. -/
noncomputable def source48CliffordGeneratorUnit
    (a : Source48Vector) [Invertible (Q a)] :
    (CliffordAlgebra Q)ˣ := by
  letI : Invertible (CliffordAlgebra.ι Q a) :=
    CliffordAlgebra.invertibleιOfInvertible Q a
  exact unitOfInvertible (CliffordAlgebra.ι Q a)

/-- The genuinely constructed degree-one Clifford unit belongs to
the ACTUAL pinned lipschitzGroup, without a surrogate subgroup. -/
noncomputable def source48CliffordGeneratorLipschitz
    (a : Source48Vector) [Invertible (Q a)] : lipschitzGroup Q := by
  let u : (CliffordAlgebra Q)ˣ := source48CliffordGeneratorUnit a
  have hu : (u : CliffordAlgebra Q) = CliffordAlgebra.ι Q a := rfl
  have hpre :
      u ∈ ((↑) ⁻¹' Set.range (CliffordAlgebra.ι Q) :
        Set (CliffordAlgebra Q)ˣ) := by
    exact ⟨a, hu.symm⟩
  have hclosure :
      u ∈ Subgroup.closure
        ((↑) ⁻¹' Set.range (CliffordAlgebra.ι Q) :
          Set (CliffordAlgebra Q)ˣ) :=
    Subgroup.subset_closure hpre
  exact ⟨u, hclosure⟩

/-- The genuine Lipschitz source action of an invertible ι(Q,a)
equals exactly the original S1V39 source rank-one matrix action. -/
theorem source48ActualLipschitzGenerator_matrixAction
    (a b : Source48Vector) [Invertible (Q a)] :
    sourceLipschitz48VectorAction (source48CliffordGeneratorLipschitz a) b =
      FCP.BFSSS1V37.source48_rankOneConjugationMatrix
        a (FCP.BFSSS1V38.source48_normalizedPolarCoeff a) *ᵥ b := by
  let : Invertible (CliffordAlgebra.ι Q a) :=
    CliffordAlgebra.invertibleιOfInvertible Q a
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q
        (sourceLipschitz48VectorAction
          (source48CliffordGeneratorLipschitz a) b) =
        ConjAct.toConjAct
          ((source48CliffordGeneratorLipschitz a : lipschitzGroup Q) :
            (CliffordAlgebra Q)ˣ) •
          (CliffordAlgebra.ι Q b) :=
      sourceLipschitz48VectorAction_clifford
        (source48CliffordGeneratorLipschitz a) b
    _ = CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b *
          ⅟(CliffordAlgebra.ι Q a) := by
      rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
      change CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b *
        CliffordAlgebra.ι Q (⅟(Q a) • a) =
          CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b *
            ⅟(CliffordAlgebra.ι Q a)
      rfl
    _ = CliffordAlgebra.ι Q
          (FCP.BFSSS1V37.source48_rankOneConjugationMatrix
             a (FCP.BFSSS1V38.source48_normalizedPolarCoeff a) *ᵥ b) :=
      (FCP.BFSSS1V39.source48_originalGeneratorMatrix_cliffordConjugation a b).symm

/-- The full actual original source real-linear Lipschitz equivalence
of the generator agrees with the exact S1V39 48×48 matrix as a map. -/
theorem source48ActualLipschitzGenerator_toLin'
    (a : Source48Vector) [Invertible (Q a)] :
    ((FCP.BFSSS1V41.sourceLipschitz48LinearEquiv
      (source48CliffordGeneratorLipschitz a) :
      Source48Vector ≃ₗ[ℝ] Source48Vector) :
      Source48Vector →ₗ[ℝ] Source48Vector) =
      Matrix.toLin'
        (FCP.BFSSS1V37.source48_rankOneConjugationMatrix
          a (FCP.BFSSS1V38.source48_normalizedPolarCoeff a)) := by
  apply LinearMap.ext
  intro b
  change sourceLipschitz48VectorAction
      (source48CliffordGeneratorLipschitz a) b =
    Matrix.toLin'
      (FCP.BFSSS1V37.source48_rankOneConjugationMatrix
        a (FCP.BFSSS1V38.source48_normalizedPolarCoeff a)) b
  rw [Matrix.toLin'_apply]
  exact source48ActualLipschitzGenerator_matrixAction a b

/-- The TRUE original Lipschitz GL48 determinant character takes
value -1 at every genuine invertible degree-one Clifford generator.
Does not yet extend sign parity over arbitrary Lipschitz products. -/
theorem source48ActualLipschitzGenerator_det
    (a : Source48Vector) [Invertible (Q a)] :
    (FCP.BFSSS1V41.sourceLipschitz48OriginalRealDetCharacter
      (source48CliffordGeneratorLipschitz a) : ℝ) = -1 := by
  change (LinearEquiv.det
    (FCP.BFSSS1V41.sourceLipschitz48LinearEquiv
      (source48CliffordGeneratorLipschitz a)) : ℝ) = -1
  rw [LinearEquiv.coe_det,
    source48ActualLipschitzGenerator_toLin',
    LinearMap.det_toLin']
  exact FCP.BFSSS1V38.source48_originalNormalizedRankOne_det a

#print axioms source48CliffordGeneratorUnit
#print axioms source48CliffordGeneratorLipschitz
#print axioms source48ActualLipschitzGenerator_matrixAction
#print axioms source48ActualLipschitzGenerator_toLin'
#print axioms source48ActualLipschitzGenerator_det

end
end FCP.BFSSS1V42
