import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18KOriginalLipschitzGradeDetIdentityAndMulProbe

/-!
K1D18L — full original Lipschitz determinant/grade identity,
by ACTUAL pinned Mathlib Subgroup.closure_induction''.

The proof uses separately qualified K generator, inverse-generator,
identity, and multiplication lemmas. It never postulates a factorization
of every Spin element or a substitute free word group.

Theorems in this source do not yet assert determinant+1 on Spin.
Spin restriction, SO48, covering, global Spin9, BFSS spectra remain
separate. CANDIDATE pending source-exact strict CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18L
noncomputable section

open FCP.BFSSS1V0
open CliffordAlgebra

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev L := lipschitzGroup Q

/-- The original Clifford involute and the *actual H determinant
character* agree throughout the original Mathlib Lipschitz closure.
No surrogates, no presumed even generator lists. -/
theorem originalSourceLipschitzGradeDetInvariant_all (s : L) :
    FCP.BFSSS1V52K1D18K.originalSourceLipschitzGradeDetInvariant s := by
  have h_all (u : Cˣ) (hu : u ∈ lipschitzGroup Q) :
      FCP.BFSSS1V52K1D18K.originalSourceLipschitzGradeDetInvariant
        (⟨u, hu⟩ : L) := by
    unfold lipschitzGroup at hu
    induction hu using Subgroup.closure_induction'' with
    | mem u hu =>
      have huL : u ∈ lipschitzGroup Q := Subgroup.subset_closure hu
      obtain ⟨a, ha⟩ := hu
      let : Invertible (CliffordAlgebra.ι Q a) := by
        rw [ha]
        exact u.invertible
      have heq : u = unitOfInvertible (CliffordAlgebra.ι Q a) := by
        apply Units.ext
        exact ha.symm
      have hsub :
          (⟨u, huL⟩ : L) =
            FCP.BFSSS1V52K1D18I.originalSourceGeneratorLipschitzUnit a := by
        apply Subtype.ext
        exact heq
      rw [hsub]
      exact FCP.BFSSS1V52K1D18K.originalSourceLipschitzGradeDetInvariant_generator a
    | inv_mem u hu =>
      have huL : u ∈ lipschitzGroup Q := Subgroup.subset_closure hu
      obtain ⟨a, ha⟩ := hu
      let : Invertible (CliffordAlgebra.ι Q a) := by
        rw [ha]
        exact u.invertible
      have heq : u = unitOfInvertible (CliffordAlgebra.ι Q a) := by
        apply Units.ext
        exact ha.symm
      have hsub :
          (⟨u⁻¹, (lipschitzGroup Q).inv_mem huL⟩ : L) =
            (FCP.BFSSS1V52K1D18I.originalSourceGeneratorLipschitzUnit a)⁻¹ := by
        apply Subtype.ext
        exact congrArg Inv.inv heq
      rw [hsub]
      exact FCP.BFSSS1V52K1D18K.originalSourceLipschitzGradeDetInvariant_generator_inv a
    | one =>
      exact FCP.BFSSS1V52K1D18K.originalSourceLipschitzGradeDetInvariant_one
    | mul u v hu hv ih_u ih_v =>
      exact FCP.BFSSS1V52K1D18K.originalSourceLipschitzGradeDetInvariant_mul
        (⟨u, hu⟩ : L) (⟨v, hv⟩ : L) ih_u ih_v
  exact h_all (s : Cˣ) s.property

#print axioms originalSourceLipschitzGradeDetInvariant_all

end
end FCP.BFSSS1V52K1D18L
