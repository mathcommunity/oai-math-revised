import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2FermionF2B2IndexedProbe

/-!
# BFSS fermions F2-B2d2 — exact upstream theta_CAR signature

Transport the kernel-verified 48-Majorana pair-indexed CAR (Gate #56)
through the existing thetaLabelEquiv bijection into the *unchanged*
thetaCandidate family. The conclusion has exactly the form and
normalization required by the pinned BFSS AlgebraData.theta_CAR field.

This is the CAR field proof only. The theta_irreducible field, full
AlgebraData 2 witness, gauge action, and physical spectral statements
remain separate unproved obligations.
-/

namespace FCP.BFSSFermionF2B2Theta
noncomputable section

open FCP.BFSSFermionF2 FCP.BFSSFermionF2B2Indexed

private abbrev BFSSOp :=
  OAI.BFSSQuantum.Fermion 2 →L[ℂ] OAI.BFSSQuantum.Fermion 2

/-- The exact CAR field required for thetaCandidate in the pinned
BFSSQuantum.AlgebraData 2 structure, with no custom assumptions. -/
theorem thetaCandidate_CAR :
    ∀ (α β : OAI.BFSSQuantum.SpinIndex)
      (A B : OAI.BFSSQuantum.ColorIndex 2),
      thetaCandidate α A * thetaCandidate β B +
        thetaCandidate β B * thetaCandidate α A =
          (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : BFSSOp) := by
  intro α β A B
  have hindex :
      (thetaLabelEquiv (α, A) = thetaLabelEquiv (β, B)) ↔
        (α = β ∧ A = B) := by
    constructor
    · intro h
      have hp : (α, A) = (β, B) := thetaLabelEquiv.injective h
      exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  change
    majoranaCandidate (thetaLabelEquiv (α, A)) *
        majoranaCandidate (thetaLabelEquiv (β, B)) +
      majoranaCandidate (thetaLabelEquiv (β, B)) *
        majoranaCandidate (thetaLabelEquiv (α, A)) =
          (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : BFSSOp)
  simpa only [hindex] using
    (majoranaCandidate_car
      (thetaLabelEquiv (α, A)) (thetaLabelEquiv (β, B)))

#print axioms thetaCandidate_CAR

end
end FCP.BFSSFermionF2B2Theta

/-!
Independent BFSS SU(2) formalization contribution by Evan T. Kotler (2026).
Research DOI: https://doi.org/10.5281/zenodo.23291242
FCP source: b60baa806dab3f0b296229a78f70e07b787544ab, experiments/openai-math-su2-concrete-potential/SU2FermionF2B2ThetaProbe.lean
Copyright (c) 2026 Evan T. Kotler. SPDX-License-Identifier: Apache-2.0.
Build status: integrated candidate; upstream port NOT YET independently verified.
OpenAI retains credit for the original BFSS definitions on which this work builds.
-/
