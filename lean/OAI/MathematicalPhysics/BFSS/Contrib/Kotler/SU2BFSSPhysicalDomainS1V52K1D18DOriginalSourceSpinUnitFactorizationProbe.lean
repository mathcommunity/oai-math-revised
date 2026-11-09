import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18CRankOneActualCliffordGeneratorProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D17OriginalSpin48IsometryActionLawsProbe

/-!
K1D18D — source-exact unit-action bridge from the genuine original
48-real Spin isometry to the genuine original rank-one Clifford generator.

The original spinGroup action is the S1V31 unique Clifford conjugation
action, packed in K1D16. The odd generator is represented as an actual
unit via unitOfInvertible, NOT incorrectly reclassified as a Spin element.

Finally, a conditional TWO-generator matrix composition identity is
proved for genuine source Spin elements with an explicitly supplied
and checked underlying unit factorization. NO existence or parity
claim for such a factorization is made here. The general source Spin
determinant +1, Lipschitz closure parity, SO48 target and covering,
global Spin9 and BFSS spectra remain open.

New source: candidate until exact strict independent CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18D
noncomputable section

open FCP.BFSSS1V0
open Matrix

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Exact S1V31 source action in its genuine K1D16 isometry
packaging satisfies the genuine unit Clifford conjugation formula. -/
theorem originalSourceSpin48Isometry_clifford_generator
    (s : spinGroup Q) (v : Source48Vector) :
    CliffordAlgebra.ι Q
      (FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry s v) =
    ConjAct.toConjAct (spinGroup.toUnits s) •
      (CliffordAlgebra.ι Q v) := by
  rw [FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry_apply]
  exact FCP.BFSSS1V31.sourceSpin48VectorAction_clifford_generator s v

/-- For the ACTUAL invertible source Clifford generator, matrix action
matches conjugation by its actual unit. This is an ODD generator
unit in the Lipschitz framework, not asserted to be in spinGroup. -/
theorem originalSourceInvertibleCliffordUnit_rankOne_action
    (a v : Source48Vector)
    [Invertible (CliffordAlgebra.ι Q a)] [Invertible (Q a)] :
    CliffordAlgebra.ι Q
      (FCP.BFSSS1V37.source48_rankOneConjugationMatrix a
        (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a) *ᵥ v) =
      ConjAct.toConjAct
        (unitOfInvertible (CliffordAlgebra.ι Q a)) •
          (CliffordAlgebra.ι Q v) := by
  rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
  change CliffordAlgebra.ι Q
      (FCP.BFSSS1V37.source48_rankOneConjugationMatrix a
        (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a) *ᵥ v) =
    CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q v *
      ⅟(CliffordAlgebra.ι Q a)
  exact FCP.BFSSS1V52K1D18C.source48_rankOneMatrix_matches_original_clifford_conjugation a v

/-- The SAME actual original Spin isometry, under a precisely
stated equality in the genuine source Clifford units, has pointwise
action by composition of the two source-exact rank-one matrices.
Existence of this factorization for arbitrary Spin elements is NOT
proved; full determinant parity remains a distinct obligation. -/
theorem originalSourceSpin48Isometry_twoGeneratorMatrices_of_unitFactorization
    (s : spinGroup Q) (a b v : Source48Vector)
    [Invertible (CliffordAlgebra.ι Q a)] [Invertible (Q a)]
    [Invertible (CliffordAlgebra.ι Q b)] [Invertible (Q b)]
    (hfactor : spinGroup.toUnits s =
      unitOfInvertible (CliffordAlgebra.ι Q a) *
        unitOfInvertible (CliffordAlgebra.ι Q b)) :
    FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry s v =
      FCP.BFSSS1V37.source48_rankOneConjugationMatrix a
        (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a) *ᵥ
      (FCP.BFSSS1V37.source48_rankOneConjugationMatrix b
        (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow b) *ᵥ v) := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q
      (FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry s v) =
      ConjAct.toConjAct (spinGroup.toUnits s) • CliffordAlgebra.ι Q v :=
        originalSourceSpin48Isometry_clifford_generator s v
    _ = ConjAct.toConjAct (unitOfInvertible (CliffordAlgebra.ι Q a)) •
        (ConjAct.toConjAct (unitOfInvertible (CliffordAlgebra.ι Q b)) •
          CliffordAlgebra.ι Q v) := by
          rw [hfactor, map_mul, mul_smul]
    _ = CliffordAlgebra.ι Q
        (FCP.BFSSS1V37.source48_rankOneConjugationMatrix a
          (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a) *ᵥ
        (FCP.BFSSS1V37.source48_rankOneConjugationMatrix b
          (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow b) *ᵥ v)) := by
          rw [← originalSourceInvertibleCliffordUnit_rankOne_action b v,
            ← originalSourceInvertibleCliffordUnit_rankOne_action a
              (FCP.BFSSS1V37.source48_rankOneConjugationMatrix b
                (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow b) *ᵥ v)]

#print axioms originalSourceSpin48Isometry_clifford_generator
#print axioms originalSourceInvertibleCliffordUnit_rankOne_action
#print axioms originalSourceSpin48Isometry_twoGeneratorMatrices_of_unitFactorization

end
end FCP.BFSSS1V52K1D18D
