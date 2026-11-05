import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V44OriginalLipschitzGradeDetParityInverseProbe

/-!
S1V45: genuine pinned Mathlib Lipschitz SUBGROUP-CLOSURE parity.
Extends original source S1V43 one/mul/generator and S1V44 inverse,
using only the exact original CliffordAlgebra.lipschitzGroup = closure
of units whose values lie in the range of CliffordAlgebra.ι.

No surrogate Pin group, finite-product assumption, scalar faithfulness,
source Spin comparison, determinant+1, global SU2 lift or spectral claim.
THREE roots; all UNQUALIFIED until strict pinned CI completes.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V45
noncomputable section

open FCP.BFSSS1V0
private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev A := CliffordAlgebra Q
private abbrev generatorPreimage : Set Aˣ :=
  ((↑) ⁻¹' Set.range (CliffordAlgebra.ι Q) : Set Aˣ)

/-- An arbitrary true original Clifford unit in the EXACT pinned generator
preimage identifies with the accepted S1V42 genuine generator, hence
satisfies the accepted grade/determinant parity relation. -/
theorem source48ActualGeneratorPreimage_gradeDetParity
    (u : Aˣ) (hu : u ∈ generatorPreimage) :
    FCP.BFSSS1V43.source48LipschitzGradeDetParity
      (⟨u, Subgroup.subset_closure hu⟩ : lipschitzGroup Q) := by
  change (u : A) ∈ Set.range (CliffordAlgebra.ι Q) at hu
  obtain ⟨a, ha⟩ := hu
  letI : Invertible (CliffordAlgebra.ι Q a) := by
    rw [ha]
    exact u.invertible
  letI : Invertible (Q a) :=
    CliffordAlgebra.invertibleOfInvertibleι Q a
  have hsame :
      (⟨u, Subgroup.subset_closure (show u ∈ generatorPreimage from ⟨a, ha⟩)⟩ :
        lipschitzGroup Q) =
      FCP.BFSSS1V42.source48CliffordGeneratorLipschitz a := by
    apply Subtype.ext
    apply Units.ext
    change (u : A) = CliffordAlgebra.ι Q a
    exact ha.symm
  rw [hsame]
  exact FCP.BFSSS1V43.source48LipschitzGradeDetParity_generator a

/-- Inverse of each actual generating unit satisfies grade/det parity,
using the strictly qualified S1V44 generic inverse interface. -/
theorem source48ActualGeneratorPreimage_inv_gradeDetParity
    (u : Aˣ) (hu : u ∈ generatorPreimage) :
    FCP.BFSSS1V43.source48LipschitzGradeDetParity
      ((⟨u, Subgroup.subset_closure hu⟩ : lipschitzGroup Q)⁻¹) :=
  FCP.BFSSS1V44.source48LipschitzGradeDetParity_inv _
    (source48ActualGeneratorPreimage_gradeDetParity u hu)

/-- Universal grade/determinant parity for EVERY element of the
ACTUAL original Mathlib Lipschitz subgroup (no Spin orientation assertion). -/
theorem source48ActualLipschitz_gradeDetParity_all
    (x : lipschitzGroup Q) :
    FCP.BFSSS1V43.source48LipschitzGradeDetParity x := by
  have hclosure :
      ∀ (u : Aˣ) (hu : u ∈ Subgroup.closure generatorPreimage),
        FCP.BFSSS1V43.source48LipschitzGradeDetParity
          (⟨u, hu⟩ : lipschitzGroup Q) := by
    intro u hu
    induction hu using Subgroup.closure_induction'' with
    | mem u hu =>
        exact source48ActualGeneratorPreimage_gradeDetParity u hu
    | inv_mem u hu =>
        exact source48ActualGeneratorPreimage_inv_gradeDetParity u hu
    | one =>
        exact FCP.BFSSS1V43.source48LipschitzGradeDetParity_one
    | mul u v hu hv ih_u ih_v =>
        exact FCP.BFSSS1V43.source48LipschitzGradeDetParity_mul
          (⟨u, hu⟩ : lipschitzGroup Q)
          (⟨v, hv⟩ : lipschitzGroup Q) ih_u ih_v
  exact hclosure (x : Aˣ) x.property

#print axioms source48ActualGeneratorPreimage_gradeDetParity
#print axioms source48ActualGeneratorPreimage_inv_gradeDetParity
#print axioms source48ActualLipschitz_gradeDetParity_all

end
end FCP.BFSSS1V45
