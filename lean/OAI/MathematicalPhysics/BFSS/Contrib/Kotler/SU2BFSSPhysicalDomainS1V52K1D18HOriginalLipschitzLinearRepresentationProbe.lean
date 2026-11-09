import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18GOriginalLipschitzVectorActionLawsProbe
import Mathlib.LinearAlgebra.Determinant

/-!
K1D18H — source-exact invertible REAL-LINEAR action and determinant
UNIT character of the ACTUAL Mathlib lipschitzGroup source48Quadratic.

Uses precisely the F action constructed from original Clifford
conjugation and the G group laws. No guessed finite generator-word
decomposition or surrogate orthogonal representation.

No determinant parity/even-spin result is asserted in this module.
Candidate until exact source hash and declaration-level strict CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18H
noncomputable section

open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev L := lipschitzGroup Q

/-- The actual source Lipschitz subgroup acts by REAL-LINEAR
EQUIVALENCES on the ORIGINAL 48-real vector space. The inverse is
the same original Clifford-conjugation action of the inverse unit. -/
noncomputable def originalSourceLipschitzLinearEquiv
    (s : L) : Source48Vector ≃ₗ[ℝ] Source48Vector where
  toFun := FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction
    (s : Cˣ) s.property
  invFun := FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction
    ((s⁻¹ : L) : Cˣ) (s⁻¹).property
  left_inv := by
    intro v
    apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
    calc
      CliffordAlgebra.ι Q
        (FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction
          ((s⁻¹ : L) : Cˣ) (s⁻¹).property
          (FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction (s : Cˣ) s.property v)) =
        ConjAct.toConjAct ((s⁻¹ : L) : Cˣ) •
          CliffordAlgebra.ι Q
            (FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction
              (s : Cˣ) s.property v) :=
        FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction_clifford_generator
          ((s⁻¹ : L) : Cˣ) (s⁻¹).property _
      _ = ConjAct.toConjAct ((s⁻¹ : L) : Cˣ) •
            (ConjAct.toConjAct (s : Cˣ) • CliffordAlgebra.ι Q v) := by
        rw [FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction_clifford_generator]
      _ = CliffordAlgebra.ι Q v := by
        rw [← mul_smul, ← map_mul]
        have hinv : ((s⁻¹ : L) : Cˣ) * (s : Cˣ) = 1 := by
          simp
        rw [hinv, map_one, one_smul]
  right_inv := by
    intro v
    apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
    calc
      CliffordAlgebra.ι Q
        (FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction
          (s : Cˣ) s.property
          (FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction
            ((s⁻¹ : L) : Cˣ) (s⁻¹).property v)) =
        ConjAct.toConjAct (s : Cˣ) •
          CliffordAlgebra.ι Q
            (FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction
              ((s⁻¹ : L) : Cˣ) (s⁻¹).property v) :=
        FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction_clifford_generator
          (s : Cˣ) s.property _
      _ = ConjAct.toConjAct (s : Cˣ) •
            (ConjAct.toConjAct ((s⁻¹ : L) : Cˣ) • CliffordAlgebra.ι Q v) := by
        rw [FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction_clifford_generator]
      _ = CliffordAlgebra.ι Q v := by
        rw [← mul_smul, ← map_mul]
        have hinv : (s : Cˣ) * ((s⁻¹ : L) : Cˣ) = 1 := by
          simp
        rw [hinv, map_one, one_smul]
  map_add' := FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction_add
    (s : Cˣ) s.property
  map_smul' := FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction_smul
    (s : Cˣ) s.property

/-- The exact original source Lipschitz equiv applies as the
unique original Clifford-conjugation vector action. -/
theorem originalSourceLipschitzLinearEquiv_apply
    (s : L) (v : Source48Vector) :
    originalSourceLipschitzLinearEquiv s v =
      FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction
        (s : Cˣ) s.property v := by
  rfl

/-- Original source Lipschitz action in the ACTUAL group order,
as a group homomorphism to REAL-LINEAR equivalences of Fin24×Fin2. -/
noncomputable def originalSourceLipschitzLinearRepresentation :
    L →* (Source48Vector ≃ₗ[ℝ] Source48Vector) where
  toFun := originalSourceLipschitzLinearEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction
      (1 : Cˣ) (lipschitzGroup Q).one_mem v = v
    exact FCP.BFSSS1V52K1D18G.sourceLipschitzVectorAction_one v
  map_mul' s t := by
    apply LinearEquiv.ext
    intro v
    change FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction
        ((s * t : L) : Cˣ) (s * t).property v =
      FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction
        (s : Cˣ) s.property
        (FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction
          (t : Cˣ) t.property v)
    exact FCP.BFSSS1V52K1D18G.sourceLipschitzVectorAction_mul
      (s : Cˣ) (t : Cˣ) s.property t.property v

/-- The genuine source Lipschitz linear representation has an
INVERTIBLE REAL DETERMINANT for every actual group element.
This is a multiplicative unit character, NOT a proven parity sign. -/
noncomputable def originalSourceLipschitzDeterminantCharacter :
    L →* ℝˣ :=
  (LinearEquiv.det :
    (Source48Vector ≃ₗ[ℝ] Source48Vector) →* ℝˣ).comp
    originalSourceLipschitzLinearRepresentation

#print axioms originalSourceLipschitzLinearEquiv
#print axioms originalSourceLipschitzLinearEquiv_apply
#print axioms originalSourceLipschitzLinearRepresentation
#print axioms originalSourceLipschitzDeterminantCharacter

end
end FCP.BFSSS1V52K1D18H
