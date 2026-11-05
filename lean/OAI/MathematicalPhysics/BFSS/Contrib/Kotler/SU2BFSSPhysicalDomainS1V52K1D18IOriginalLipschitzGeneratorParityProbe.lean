import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18HOriginalLipschitzLinearRepresentationProbe

/-!
K1D18I — source-exact generator boundary of the TRUE Lipschitz
determinant unit character and Clifford grade involution.

For an actual invertible ORIGINAL Clifford generator ι Q a, derive
invertibility of its ORIGINAL source quadratic value using the pinned
Mathlib invertibleOfInvertibleι, not an independent new assumption.
Construct its actual membership in the original lipschitzGroup
Subgroup.closure, identify the true H linear representation with the
accepted S1V37 source rank-one matrix, prove its determinant equals
-1, and verify that original Clifford involution negates this generator.

This is the GENERATOR case only. Closure induction, unit inverse,
multiplication, all-even Spin determinant +1, SO48, covering, global
Spin9 and spectra remain separate.
CANDIDATE pending independent source/hash/axiom strict CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18I
noncomputable section

open FCP.BFSSS1V0
open CliffordAlgebra
open Matrix

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev L := lipschitzGroup Q

/-- Any actual unit built from an invertible original Clifford
generator is a genuine member of Mathlib's source Lipschitz closure. -/
theorem originalSourceGeneratorUnit_mem_lipschitz
    (a : Source48Vector) [Invertible (CliffordAlgebra.ι Q a)] :
    unitOfInvertible (CliffordAlgebra.ι Q a) ∈ lipschitzGroup Q := by
  unfold lipschitzGroup
  apply Subgroup.subset_closure
  change ((unitOfInvertible (CliffordAlgebra.ι Q a) : Cˣ) : C) ∈
    Set.range (CliffordAlgebra.ι Q)
  exact ⟨a, rfl⟩

/-- The actual original Clifford-vector unit inside the actual
source Lipschitz subgroup. This is not asserted to be Spin-even. -/
noncomputable def originalSourceGeneratorLipschitzUnit
    (a : Source48Vector) [Invertible (CliffordAlgebra.ι Q a)] : L :=
  ⟨unitOfInvertible (CliffordAlgebra.ι Q a),
    originalSourceGeneratorUnit_mem_lipschitz a⟩

/-- Source polar row with its quadratic invertibility DERIVED from
invertibility of the same original Clifford generator. -/
private noncomputable def sourceGeneratorPolarRow
    (a : Source48Vector) [Invertible (CliffordAlgebra.ι Q a)] :
    Source48Vector :=
  letI : Invertible (Q a) := invertibleOfInvertibleι Q a
  FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a

/-- The H representation of an actual ORIGINAL generator unit is the
genuine S1V37 rank-one original 48-coordinate matrix. Invertibility
of Q a is DERIVED from invertibility of original Clifford ι Q a. -/
theorem originalSourceGeneratorLipschitzLinearMap_eq_rankOne
    (a : Source48Vector) [Invertible (CliffordAlgebra.ι Q a)] :
    ((FCP.BFSSS1V52K1D18H.originalSourceLipschitzLinearEquiv
        (originalSourceGeneratorLipschitzUnit a) :
        Source48Vector ≃ₗ[ℝ] Source48Vector) :
      Source48Vector →ₗ[ℝ] Source48Vector) =
    Matrix.toLin'
      (FCP.BFSSS1V37.source48_rankOneConjugationMatrix a
        (sourceGeneratorPolarRow a)) := by
  let : Invertible (Q a) := invertibleOfInvertibleι Q a
  apply LinearMap.ext
  intro v
  change FCP.BFSSS1V52K1D18H.originalSourceLipschitzLinearEquiv
      (originalSourceGeneratorLipschitzUnit a) v =
    Matrix.toLin'
      (FCP.BFSSS1V37.source48_rankOneConjugationMatrix a
        (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a)) v
  rw [Matrix.toLin'_apply]
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q
      (FCP.BFSSS1V52K1D18H.originalSourceLipschitzLinearEquiv
        (originalSourceGeneratorLipschitzUnit a) v) =
      ConjAct.toConjAct
        ((originalSourceGeneratorLipschitzUnit a : L) : Cˣ) •
        CliffordAlgebra.ι Q v := by
          rw [FCP.BFSSS1V52K1D18H.originalSourceLipschitzLinearEquiv_apply]
          exact FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction_clifford_generator
            _ _ v
    _ = CliffordAlgebra.ι Q
      (FCP.BFSSS1V37.source48_rankOneConjugationMatrix a
        (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a) *ᵥ v) := by
          change ConjAct.toConjAct
              (unitOfInvertible (CliffordAlgebra.ι Q a)) •
              CliffordAlgebra.ι Q v = _
          exact (FCP.BFSSS1V52K1D18D.originalSourceInvertibleCliffordUnit_rankOne_action
            a v).symm

/-- The determinant UNIT character of the genuine original-source
Lipschitz representation is -1 on EVERY invertible original
Clifford-vector generator. This is not a universal parity theorem. -/
theorem originalSourceGeneratorLipschitzDeterminant_neg_one
    (a : Source48Vector) [Invertible (CliffordAlgebra.ι Q a)] :
    ((FCP.BFSSS1V52K1D18H.originalSourceLipschitzDeterminantCharacter
      (originalSourceGeneratorLipschitzUnit a) : ℝˣ) : ℝ) = -1 := by
  let : Invertible (Q a) := invertibleOfInvertibleι Q a
  change ((LinearEquiv.det
    (FCP.BFSSS1V52K1D18H.originalSourceLipschitzLinearEquiv
      (originalSourceGeneratorLipschitzUnit a)) : ℝˣ) : ℝ) = (-1 : ℝ)
  rw [LinearEquiv.coe_det,
    originalSourceGeneratorLipschitzLinearMap_eq_rankOne,
    LinearMap.det_toLin']
  change (FCP.BFSSS1V37.source48_rankOneConjugationMatrix a
    (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a)).det = (-1 : ℝ)
  exact FCP.BFSSS1V52K1D18C.source48_original_generator_rankOneMatrix_det a

/-- The original grade involution negates each genuine original
Clifford generator unit, as an equality in the original Clifford
algebra. No even-parity assumption on this odd generator. -/
theorem originalSourceGeneratorLipschitzUnit_involute_neg
    (a : Source48Vector) [Invertible (CliffordAlgebra.ι Q a)] :
    CliffordAlgebra.involute
      (((originalSourceGeneratorLipschitzUnit a : L) : Cˣ) : C) =
      -(((originalSourceGeneratorLipschitzUnit a : L) : Cˣ) : C) := by
  change CliffordAlgebra.involute (CliffordAlgebra.ι Q a) =
    -(CliffordAlgebra.ι Q a)
  exact CliffordAlgebra.involute_ι a

#print axioms originalSourceGeneratorUnit_mem_lipschitz
#print axioms originalSourceGeneratorLipschitzUnit
#print axioms originalSourceGeneratorLipschitzLinearMap_eq_rankOne
#print axioms originalSourceGeneratorLipschitzDeterminant_neg_one
#print axioms originalSourceGeneratorLipschitzUnit_involute_neg

end
end FCP.BFSSS1V52K1D18I
