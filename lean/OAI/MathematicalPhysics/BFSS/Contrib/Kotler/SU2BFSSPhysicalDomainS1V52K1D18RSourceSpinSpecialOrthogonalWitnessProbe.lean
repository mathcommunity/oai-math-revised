import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18POriginalSpinQuadraticIsometryDetOneProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D14OriginalSpin48LinearRepresentationKernelProbe

/-!
K1D18R — a genuinely distinct, source-exact structural-witness route.
Use the ORIGINAL K1D16 source48Quadratic isometries themselves
as witnesses in the same original GL48, instead of repeatedly
reducing the full 48-coordinate preservation predicate. The
isometries are source-typed, not surrogate matrices or a new action.

An equivalence with Q's predicate-based quadratic-preserving GL
subgroup, the SO-valued homomorphism and transport of the proven
two-sign GL kernel remain separate obligations. Candidate only.
-/
set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18R
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev GL48 := Source48Vector ≃ₗ[ℝ] Source48Vector

/-- Subgroup of the REAL original 48-vector linear equivalences
carrying a witness that it is a Q-isometry, with Q exactly the
source original form and no other metric or coordinate ordering. -/
noncomputable def source48QuadraticIsometryWitnessGL : Subgroup GL48 where
  carrier := {f | ∃ i : Q.IsometryEquiv Q, (i : GL48) = f}
  one_mem' := by
    refine ⟨QuadraticMap.IsometryEquiv.refl Q, ?_⟩
    rfl
  mul_mem' := by
    intro f g hf hg
    rcases hf with ⟨i, hi⟩
    rcases hg with ⟨j, hj⟩
    refine ⟨j.trans i, ?_⟩
    have hMul :
        ((j.trans i : Q.IsometryEquiv Q) : GL48) =
          (i : GL48) * (j : GL48) := by
      apply LinearEquiv.ext
      intro v
      rfl
    calc
      ((j.trans i : Q.IsometryEquiv Q) : GL48) =
          (i : GL48) * (j : GL48) := hMul
      _ = f * g := by rw [hi, hj]
  inv_mem' := by
    intro f hf
    rcases hf with ⟨i, hi⟩
    refine ⟨i.symm, ?_⟩
    have hInv :
        ((i.symm : Q.IsometryEquiv Q) : GL48) =
          ((i : GL48)⁻¹) := by
      apply LinearEquiv.ext
      intro v
      rfl
    calc
      ((i.symm : Q.IsometryEquiv Q) : GL48) =
          ((i : GL48)⁻¹) := hInv
      _ = f⁻¹ := by rw [hi]

/-- Original source-isometry witnesses, restricted to determinant +1. -/
noncomputable def source48SpecialOrthogonalWitnessGL : Subgroup GL48 :=
  source48QuadraticIsometryWitnessGL ⊓
    (LinearEquiv.det : GL48 →* ℝˣ).ker

/-- K1D16 directly witnesses membership of the same original
K1D13 real-linear Spin action in the original isometry image. -/
theorem originalSourceSpin48_mem_isometryWitness
    (s : spinGroup Q) :
    FCP.BFSSS1V52K1D13.originalSourceSpin48LinearRepresentation s ∈
      source48QuadraticIsometryWitnessGL := by
  refine ⟨FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry s, ?_⟩
  exact FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry_underlyingLinearEquiv s

/-- Structural source-exact SO membership: K1D16 original
quadratic isometry witness, plus accepted O/P determinant +1. -/
theorem originalSourceSpin48_mem_specialOrthogonalWitness
    (s : spinGroup Q) :
    FCP.BFSSS1V52K1D13.originalSourceSpin48LinearRepresentation s ∈
      source48SpecialOrthogonalWitnessGL := by
  constructor
  · exact originalSourceSpin48_mem_isometryWitness s
  · change (LinearEquiv.det
      (FCP.BFSSS1V52K1D13.originalSourceSpin48LinearEquiv s) : ℝˣ) = 1
    apply Units.ext
    change ((LinearEquiv.det
      (FCP.BFSSS1V52K1D13.originalSourceSpin48LinearEquiv s) : ℝˣ) : ℝ) = 1
    rw [LinearEquiv.coe_det,
      FCP.BFSSS1V52K1D18O.originalSourceSpin48_linearEquiv_coe_eq_sourceLinearMap]
    exact FCP.BFSSS1V52K1D18O.originalSourceSpin48_originalLinearMap_det_one s

#print axioms source48QuadraticIsometryWitnessGL
#print axioms source48SpecialOrthogonalWitnessGL
#print axioms originalSourceSpin48_mem_isometryWitness
#print axioms originalSourceSpin48_mem_specialOrthogonalWitness

end
end FCP.BFSSS1V52K1D18R
