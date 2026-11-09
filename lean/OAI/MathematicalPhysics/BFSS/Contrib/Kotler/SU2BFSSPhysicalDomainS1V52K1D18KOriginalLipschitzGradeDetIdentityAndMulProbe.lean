import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18JOriginalLipschitzInverseGeneratorParityProbe

/-!
K1D18K — original Lipschitz grade/determinant invariant:
the generator, inverse-generator, identity, and multiplication cases.

All terms use the genuine 48-real source Clifford algebra, genuine
lipschitzGroup source48Quadratic, and accepted H determinant-unit
character. No replacement action, surreptitious finite-word assumption,
parity conclusion for all Lipschitz units, Spin orientation, topology,
or BFSS spectral claim.

The Subgroup.closure_induction'' combination remains separately gated.
Candidate until strict fresh compilation and axiom/type audit.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18K
noncomputable section

open FCP.BFSSS1V0
open CliffordAlgebra

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev L := lipschitzGroup Q
private abbrev chi := FCP.BFSSS1V52K1D18H.originalSourceLipschitzDeterminantCharacter

/-- The precise source-exact parity invariant over actual Lipschitz
units. Clifford grade involution is compared with the REAL scalar
of the H determinant UNIT character, not a made-up sign character. -/
def originalSourceLipschitzGradeDetInvariant (s : L) : Prop :=
  CliffordAlgebra.involute (((s : Cˣ) : C)) =
    (((chi s : ℝˣ) : ℝ)) • (((s : Cˣ) : C))

/-- Unit identity case of the genuine source Lipschitz invariant. -/
theorem originalSourceLipschitzGradeDetInvariant_one :
    originalSourceLipschitzGradeDetInvariant (1 : L) := by
  unfold originalSourceLipschitzGradeDetInvariant
  simp

/-- The TRUE original 48-real invertible Clifford generator
satisfies the grade/determinant invariant. -/
theorem originalSourceLipschitzGradeDetInvariant_generator
    (a : Source48Vector) [Invertible (CliffordAlgebra.ι Q a)] :
    originalSourceLipschitzGradeDetInvariant
      (FCP.BFSSS1V52K1D18I.originalSourceGeneratorLipschitzUnit a) := by
  unfold originalSourceLipschitzGradeDetInvariant
  rw [FCP.BFSSS1V52K1D18I.originalSourceGeneratorLipschitzUnit_involute_neg,
    FCP.BFSSS1V52K1D18I.originalSourceGeneratorLipschitzDeterminant_neg_one]
  simp

/-- Inverse ORIGINAL generator case of the genuine invariant.
This is the already qualified J inverse identity, not a claimed
involution identity for arbitrary Clifford elements. -/
theorem originalSourceLipschitzGradeDetInvariant_generator_inv
    (a : Source48Vector) [Invertible (CliffordAlgebra.ι Q a)] :
    originalSourceLipschitzGradeDetInvariant
      (FCP.BFSSS1V52K1D18I.originalSourceGeneratorLipschitzUnit a)⁻¹ := by
  unfold originalSourceLipschitzGradeDetInvariant
  exact FCP.BFSSS1V52K1D18J.originalSourceGeneratorInverse_grade_det_agreement a

/-- Multiplicative stability of the exact grade/determinant invariant
for genuine source Lipschitz elements. The accepted H determinant
character is a monoid hom; the original Clifford involute is an
algebra hom. This proof does NOT assume a finite word decomposition. -/
theorem originalSourceLipschitzGradeDetInvariant_mul
    (s t : L)
    (hs : originalSourceLipschitzGradeDetInvariant s)
    (ht : originalSourceLipschitzGradeDetInvariant t) :
    originalSourceLipschitzGradeDetInvariant (s * t) := by
  unfold originalSourceLipschitzGradeDetInvariant at hs ht ⊢
  have hchar :
      (((chi (s * t) : ℝˣ) : ℝ)) =
        (((chi s : ℝˣ) : ℝ)) * (((chi t : ℝˣ) : ℝ)) := by
    rw [map_mul, Units.val_mul]
  change CliffordAlgebra.involute
      ((((s : Cˣ) : C)) * (((t : Cˣ) : C))) =
    (((chi (s * t) : ℝˣ) : ℝ)) •
      ((((s : Cˣ) : C)) * (((t : Cˣ) : C)))
  rw [hchar]
  calc
    CliffordAlgebra.involute
        ((((s : Cˣ) : C)) * (((t : Cˣ) : C))) =
      CliffordAlgebra.involute (((s : Cˣ) : C)) *
        CliffordAlgebra.involute (((t : Cˣ) : C)) := map_mul _ _ _
    _ = ((((chi s : ℝˣ) : ℝ)) • (((s : Cˣ) : C))) *
          ((((chi t : ℝˣ) : ℝ)) • (((t : Cˣ) : C))) := by rw [hs, ht]
    _ = ((((chi s : ℝˣ) : ℝ)) * (((chi t : ℝˣ) : ℝ))) •
          ((((s : Cˣ) : C)) * (((t : Cˣ) : C))) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]

#print axioms originalSourceLipschitzGradeDetInvariant
#print axioms originalSourceLipschitzGradeDetInvariant_one
#print axioms originalSourceLipschitzGradeDetInvariant_generator
#print axioms originalSourceLipschitzGradeDetInvariant_generator_inv
#print axioms originalSourceLipschitzGradeDetInvariant_mul

end
end FCP.BFSSS1V52K1D18K
