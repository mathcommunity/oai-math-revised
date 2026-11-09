import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V0StandaloneOrthogonalGeometryProbe
import Mathlib.Logic.Equiv.Fin.Basic

/-!
S1V5 — concrete 16 × 3 enumeration of actual source Majorana labels.

The original source color-Fock indexing is 8 complex spin pairs ×
3 colors × 2 real Majorana components, i.e. 16 real spin labels ×
3 colors. This file constructs the exact elementary index equivalence
and independently identifiable coordinate axes on the same
(Fin 24 × Fin 2) source-size label type. It is the combinatorial
ingredient for a non-surrogate 16-block source Spin construction.

A later ORIGINAL source-label theorem must identify this explicit
enumeration with accepted colorModeEquiv and spinPairEquiv: none
of those original definitions is imported or silently assumed here.

CANDIDATE until strict pinned Mathlib CI.
-/

set_option autoImplicit false
set_option maxHeartbeats 280000

namespace FCP.BFSSS1V5
noncomputable section

open FCP.BFSSS1V0

abbrev RealSpinBlock := Fin 8 × Fin 2
abbrev ColorLabel := Fin 3
abbrev SourceLabel := Fin 24 × Fin 2

/-- The explicit exact 8×3 → 24 Fock-mode packing; naming the type
prevents Lean from inventing metavariables for the inverse sizes. -/
noncomputable def sourceColorModeEquiv : Fin 8 × Fin 3 ≃ Fin 24 :=
  finProdFinEquiv

/-- An explicit choice of 16-by-3 real Majorana coordinate ordering.
The linear array index is color + 3 * complex-spin-pair number;
the real/imaginary Majorana bit is left unchanged. -/
noncomputable def sourceBlockColorEquiv :
    (RealSpinBlock × ColorLabel) ≃ SourceLabel where
  toFun p := (sourceColorModeEquiv (p.1.1, p.2), p.1.2)
  invFun p := (((sourceColorModeEquiv.symm p.1).1, p.2),
               (sourceColorModeEquiv.symm p.1).2)
  left_inv := by
    rintro ⟨⟨j, s⟩, A⟩
    simp
  right_inv := by
    rintro ⟨m, s⟩
    simp

/-- A source-sized coordinate label associated to one of the
sixteen real spin blocks and a three-color position. -/
noncomputable def sourceBlockColorLabel
    (α : RealSpinBlock) (A : ColorLabel) : SourceLabel :=
  sourceBlockColorEquiv (α, A)

/-- Different block/color pairs have different actual 48-label
Majorana indices, with no independent dimension postulate. -/
theorem sourceBlockColorLabel_injective :
    Function.Injective
      (fun p : RealSpinBlock × ColorLabel =>
        sourceBlockColorLabel p.1 p.2) := by
  intro p q h
  exact sourceBlockColorEquiv.injective h

/-- Each concrete block-color index has an elementary source 48-real
coordinate axis, on EXACTLY the S1V0 input space. -/
noncomputable def sourceBlockColorAxis
    (α : RealSpinBlock) (A : ColorLabel) : Source48Vector :=
  Pi.single (sourceBlockColorLabel α A) (1 : ℝ)

theorem sourceBlockColorAxis_self
    (α : RealSpinBlock) (A : ColorLabel) :
    sourceBlockColorAxis α A (sourceBlockColorLabel α A) = 1 := by
  simp [sourceBlockColorAxis]

theorem sourceBlockColorAxis_other
    (p q : RealSpinBlock × ColorLabel) (hpq : p ≠ q) :
    sourceBlockColorAxis p.1 p.2
      (sourceBlockColorLabel q.1 q.2) = 0 := by
  have hlabel : sourceBlockColorLabel p.1 p.2 ≠
        sourceBlockColorLabel q.1 q.2 := by
    intro h
    exact hpq (sourceBlockColorLabel_injective h)
  simp [sourceBlockColorAxis, hlabel]

#print axioms sourceColorModeEquiv
#print axioms sourceBlockColorEquiv
#print axioms sourceBlockColorLabel_injective
#print axioms sourceBlockColorAxis_self
#print axioms sourceBlockColorAxis_other

end
end FCP.BFSSS1V5
