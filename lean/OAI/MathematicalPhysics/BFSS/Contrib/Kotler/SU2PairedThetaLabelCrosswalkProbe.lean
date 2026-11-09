import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2FermionF2B2ThetaProbe

/-!
# Original G1A paired-spin labeling versus the older thetaLabelEquiv

The three source-index equivalence definitions below reproduce the explicit
G1A formulas from FCP SU2BFSSG1APairedThetaProbe.lean:
spinPairEquiv, colorModeEquiv, and pairedLabelEquiv.  The older
thetaLabelEquiv instead uses Fintype.equivFin and must NOT be identified
definitionally with pairedLabelEquiv.

This module proves the *actual permutation* and relabeling of the concrete
Fock Majorana operators, preserving the original BFSS SpinIndex and
ColorIndex 2.  It does not import or claim the entire independent G1A
full AlgebraData witness; no global Spin48 / Spin9 result is claimed.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedThetaLabelCrosswalk
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSFermionF1 FCP.BFSSFermionF2

/-- Exact G1A spin-pair packing; no Fintype.equivFin ordering guess. -/
noncomputable def spinPairEquiv : SpinIndex ≃ (Fin 8 × Fin 2) :=
  (finProdFinEquiv : (Fin 8 × Fin 2) ≃ Fin (8 * 2)).symm

/-- Exact G1A eight-by-three complex Fock mode packing. -/
noncomputable def colorModeEquiv :
    (Fin 8 × ColorIndex 2) ≃ Fin 24 :=
  finProdFinEquiv

/-- Exact G1A source formula, copied at the level of real 48 labels. -/
noncomputable def pairedLabelEquiv :
    (SpinIndex × ColorIndex 2) ≃ (Fin 24 × Fin 2) where
  toFun p :=
    (colorModeEquiv ((spinPairEquiv p.1).1, p.2), (spinPairEquiv p.1).2)
  invFun p :=
    (spinPairEquiv.symm ((colorModeEquiv.symm p.1).1, p.2),
      (colorModeEquiv.symm p.1).2)
  left_inv := by
    rintro ⟨α, A⟩
    simp
  right_inv := by
    rintro ⟨m, r⟩
    simp

/-- An explicit, invertible permutation from paired-source spin/color
labels into the older thetaCandidate input ordering. -/
noncomputable def pairedToOldLabel :
    (SpinIndex × ColorIndex 2) ≃ (SpinIndex × ColorIndex 2) :=
  pairedLabelEquiv.trans thetaLabelEquiv.symm

theorem pairedToOldLabel_correct (α : SpinIndex) (A : ColorIndex 2) :
    thetaLabelEquiv (pairedToOldLabel (α, A)) =
      pairedLabelEquiv (α, A) := by
  change thetaLabelEquiv (thetaLabelEquiv.symm
    (pairedLabelEquiv (α, A))) = pairedLabelEquiv (α, A)
  exact Equiv.apply_symm_apply _ _

/-- This is the source-exact paired-index *candidate* built from the
existing, independently qualified 48 Fock Majorana family. -/
noncomputable def pairedTheta (α : SpinIndex) (A : ColorIndex 2) :
    Fermion 2 →L[ℂ] Fermion 2 :=
  majoranaCandidate (pairedLabelEquiv (α, A))

/-- The paired family is the old theta family reindexed by an explicit
permutation, not the pointwise identity of their index maps. -/
theorem pairedTheta_eq_reindexed_old (α : SpinIndex) (A : ColorIndex 2) :
    pairedTheta α A =
      thetaCandidate (pairedToOldLabel (α, A)).1
        (pairedToOldLabel (α, A)).2 := by
  change majoranaCandidate (pairedLabelEquiv (α, A)) =
    majoranaCandidate (thetaLabelEquiv (pairedToOldLabel (α, A)))
  rw [pairedToOldLabel_correct]

/-- Exact delta-one CAR for the G1A-indexed candidate, without any
unproved equality between pairedLabelEquiv and thetaLabelEquiv. -/
theorem pairedTheta_CAR (α β : SpinIndex) (A B : ColorIndex 2) :
    pairedTheta α A * pairedTheta β B +
      pairedTheta β B * pairedTheta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Fermion 2 →L[ℂ] Fermion 2) := by
  have hindex :
      (pairedLabelEquiv (α, A) = pairedLabelEquiv (β, B)) ↔
        (α = β ∧ A = B) := by
    constructor
    · intro h
      have hp : (α, A) = (β, B) := pairedLabelEquiv.injective h
      exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  change
    majoranaCandidate (pairedLabelEquiv (α, A)) *
        majoranaCandidate (pairedLabelEquiv (β, B)) +
      majoranaCandidate (pairedLabelEquiv (β, B)) *
        majoranaCandidate (pairedLabelEquiv (α, A)) =
          (if α = β ∧ A = B then (1 : ℂ) else 0) •
            (1 : Fermion 2 →L[ℂ] Fermion 2)
  simpa only [hindex] using
    (FCP.BFSSFermionF2B2Indexed.majoranaCandidate_car
      (pairedLabelEquiv (α, A)) (pairedLabelEquiv (β, B)))

theorem pairedTheta_selfAdjoint (α : SpinIndex) (A : ColorIndex 2) :
    IsSelfAdjoint (pairedTheta α A) := by
  exact majoranaCandidate_selfAdjoint (pairedLabelEquiv (α, A))

#print axioms pairedToOldLabel_correct
#print axioms pairedTheta_eq_reindexed_old
#print axioms pairedTheta_CAR
#print axioms pairedTheta_selfAdjoint

end
end FCP.BFSSPairedThetaLabelCrosswalk

/-!
Independent BFSS source-index crosswalk by Evan T. Kotler / OpenAI (2026).
Index formulas sourced from FCP SU2BFSSG1APairedThetaProbe.lean,
Git blob 4f8fbf05a35c1d625746931b7ff0361b7ffc2ec4.
No upstream mathcommunity PR is authorized.
Copyright (c) 2026 Evan T. Kotler. SPDX-License-Identifier: Apache-2.0.
-/
