import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9D7OriginalNativeFockMajorana48MatrixBlockEntryProbe

/-!
S1V52L9D8 — STAGED until a strict source-pinned Lean/axiom gate.
Translate the accepted actual 48-real original Fock Majorana MATRIX
entry formula L9D7 into its action on the SAME original 16×3
source-coordinate Majorana basis as the accepted canonical Spin48
action L9D6.

Use the pinned Mathlib Matrix.mulVec_single_one theorem, avoiding
unnecessary expansion of 48×48 matrix multiplication. Test output
row/input column precisely, and preserve the original Fock
real/imaginary Majorana bit.

One candidate root. No claim about arbitrary vectors or universal
sourceSpin48CoversActualGauge until separately kernel-qualified.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52L9D8
noncomputable section

open OAI.BFSSQuantum
open Matrix
open FCP.BFSSS1V5
open FCP.BFSSS1V52L9D7
open FCP.BFSSSU2GaugeG3A
open FCP.BFSSSU2PhysicalDomainS1J

/-- Actual original BFSS Fock 48-real Majorana matrix acts on
each source block/color basis axis by its genuine native
adjointColorMatrix column; this is the source-side mulVec theorem,
NOT an invented SO48 surrogate. -/
theorem originalSourceRealMajoranaMatrix_mulVec_sourceAxis
    (g : GaugeGroup 2) (α : RealSpinBlock) (A : Fin 3) :
    (sourceRealMajoranaMatrix g).mulVec (sourceBlockColorAxis α A) =
      ∑ B : Fin 3,
        (adjointColorMatrix g B A) • sourceBlockColorAxis α B := by
  classical
  change (sourceRealMajoranaMatrix g *ᵥ
      Pi.single (sourceBlockColorLabel α A) (1 : ℝ)) =
    ∑ B : Fin 3,
      (adjointColorMatrix g B A) • sourceBlockColorAxis α B
  rw [Matrix.mulVec_single_one]
  funext p
  obtain ⟨⟨β, C⟩, rfl⟩ := sourceBlockColorEquiv.surjective p
  change sourceRealMajoranaMatrix g
      (sourceBlockColorLabel β C) (sourceBlockColorLabel α A) =
    (∑ B : Fin 3, (adjointColorMatrix g B A) •
      sourceBlockColorAxis α B) (sourceBlockColorLabel β C)
  rw [originalSourceRealMajoranaMatrix_sourceBlock_entry]
  -- Exact original source-label injectivity reduces the ONE
  -- coordinate indicator; avoid unfolding the whole Fock index
  -- equivalence or relying on nonexistent Prod.mk.inj_iff.mp.
  have hcoord (B : Fin 3) :
      sourceBlockColorAxis α B (sourceBlockColorLabel β C) =
        if α = β ∧ B = C then (1 : ℝ) else 0 := by
    have hlabel :
        (sourceBlockColorLabel β C = sourceBlockColorLabel α B) ↔
          (α = β ∧ B = C) := by
      constructor
      · intro h
        have hp : (β, C) = (α, B) :=
          sourceBlockColorLabel_injective h
        exact ⟨(congrArg Prod.fst hp).symm,
          (congrArg Prod.snd hp).symm⟩
      · rintro ⟨rfl, rfl⟩
        rfl
    simp only [sourceBlockColorAxis, Pi.single_apply]
    -- The two if-conditions are logically equivalent, but rewriting
    -- the proposition with rw fails because the Decidable instance
    -- of ite depends on the actual *original* equality proposition.
    -- Case-split instead; both conditions reduce definitionally.
    by_cases h : α = β ∧ B = C
    · have heq : sourceBlockColorLabel β C =
          sourceBlockColorLabel α B := hlabel.mpr h
      simp only [_root_.ite_eq_left heq, _root_.ite_eq_left h]
    · have hne : ¬ (sourceBlockColorLabel β C =
          sourceBlockColorLabel α B) := by
        intro heq
        exact h (hlabel.mp heq)
      simp only [_root_.ite_eq_right hne, _root_.ite_eq_right h]
  -- Compute only the three ORIGINAL color coordinates. Restrict
  -- simplification to this scalar sum, not original BFSS definitions.
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [hcoord]
  by_cases hab : β = α
  · subst β
    simp only [true_and, ite_true,
      mul_ite, mul_one, mul_zero]
    simp
  · have hba : α ≠ β := Ne.symm hab
    simp only [hab, hba, false_and, ite_false,
      mul_zero, Finset.sum_const_zero]

#print axioms originalSourceRealMajoranaMatrix_mulVec_sourceAxis

end
end FCP.BFSSS1V52L9D8
