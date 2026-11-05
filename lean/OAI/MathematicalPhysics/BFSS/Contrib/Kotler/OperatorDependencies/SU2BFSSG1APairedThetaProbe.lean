import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSFullAlgebraDataProbe

/-!
# BFSS SU(2) G1-A — explicit spin-paired color-preserving theta family

Use the accepted 24-mode Fock Majoranas, generic CAR and irreducibility.
Unlike the previous Fintype.equivFin labeling, this convention pairs
the two Majoranas of mode (j,A) at spins (j,0) and (j,1).

The previous concreteAlgebraData is kept unchanged. No gauge group
representation, physicalSpace or spectral result is constructed here.
-/

namespace FCP.BFSSSU2GaugeG1A
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSFermionF1 FCP.BFSSFermionF2
open FCP.BFSSSU2Full

/-- Split the sixteen spin labels into eight complex-mode pairs.
Using finProdFinEquiv avoids the unspecified ordering of equivFin. -/
noncomputable def spinPairEquiv : SpinIndex ≃ (Fin 8 × Fin 2) :=
  (finProdFinEquiv : (Fin 8 × Fin 2) ≃ Fin (8 * 2)).symm

/-- An explicit eight-by-three labeling of all twenty-four Fock modes. -/
noncomputable def colorModeEquiv :
    (Fin 8 × ColorIndex 2) ≃ Fin 24 :=
  finProdFinEquiv

/-- The exact 48-label map: same mode for spin pair j and color A. -/
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

/-- Even spin label selects the real Majorana of the mode (j,A). -/
theorem pairedLabel_even (j : Fin 8) (A : ColorIndex 2) :
    pairedLabelEquiv (spinPairEquiv.symm (j, (0 : Fin 2)), A) =
      (colorModeEquiv (j,A), (0 : Fin 2)) := by
  simp [pairedLabelEquiv]

/-- Odd spin label selects the imaginary Majorana of the SAME mode. -/
theorem pairedLabel_odd (j : Fin 8) (A : ColorIndex 2) :
    pairedLabelEquiv (spinPairEquiv.symm (j, (1 : Fin 2)), A) =
      (colorModeEquiv (j,A), (1 : Fin 2)) := by
  simp [pairedLabelEquiv]

/-- The actual accepted self-adjoint Majoranas, explicitly relabeled. -/
noncomputable def pairedTheta (α : SpinIndex) (A : ColorIndex 2) :
    Fermion 2 →L[ℂ] Fermion 2 :=
  majoranaCandidate (pairedLabelEquiv (α,A))

theorem pairedTheta_even (j : Fin 8) (A : ColorIndex 2) :
    pairedTheta (spinPairEquiv.symm (j, (0 : Fin 2))) A =
      majorana0 (colorModeEquiv (j,A)) := by
  rw [pairedTheta, pairedLabel_even]
  simp [majoranaCandidate]

theorem pairedTheta_odd (j : Fin 8) (A : ColorIndex 2) :
    pairedTheta (spinPairEquiv.symm (j, (1 : Fin 2))) A =
      majorana1 (colorModeEquiv (j,A)) := by
  rw [pairedTheta, pairedLabel_odd]
  simp [majoranaCandidate]

theorem pairedTheta_selfAdjoint :
    ∀ (α : SpinIndex) (A : ColorIndex 2),
      IsSelfAdjoint (pairedTheta α A) := by
  intro α A
  exact majoranaCandidate_selfAdjoint (pairedLabelEquiv (α,A))

/-- Exact delta-one 48-Majorana CAR for the paired family. -/
theorem pairedTheta_CAR
    (α β : SpinIndex) (A B : ColorIndex 2) :
    pairedTheta α A * pairedTheta β B +
      pairedTheta β B * pairedTheta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Fermion 2 →L[ℂ] Fermion 2) := by
  have hindex :
      (pairedLabelEquiv (α,A) = pairedLabelEquiv (β,B)) ↔
        (α = β ∧ A = B) := by
    constructor
    · intro h
      have hp : (α,A) = (β,B) := pairedLabelEquiv.injective h
      exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  change
    majoranaCandidate (pairedLabelEquiv (α,A)) *
        majoranaCandidate (pairedLabelEquiv (β,B)) +
      majoranaCandidate (pairedLabelEquiv (β,B)) *
        majoranaCandidate (pairedLabelEquiv (α,A)) =
          (if α = β ∧ A = B then (1 : ℂ) else 0) •
            (1 : Fermion 2 →L[ℂ] Fermion 2)
  simpa only [hindex] using
    (FCP.BFSSFermionF2B2Indexed.majoranaCandidate_car
      (pairedLabelEquiv (α,A)) (pairedLabelEquiv (β,B)))

/-- Relabeling all 48 generators cannot create invariant submodules. -/
theorem pairedTheta_irreducible :
    ∀ W : Submodule ℂ (Fermion 2),
      (∀ α A, ∀ w ∈ W, pairedTheta α A w ∈ W) →
        W = ⊥ ∨ W = ⊤ := by
  intro W hθ
  have hOld : ∀ α A, ∀ w ∈ W, thetaCandidate α A w ∈ W := by
    intro α A w hw
    let q := pairedLabelEquiv.symm (thetaLabelEquiv (α,A))
    have hq := hθ q.1 q.2 w hw
    change majoranaCandidate (pairedLabelEquiv q) w ∈ W at hq
    have hlabel : pairedLabelEquiv q = thetaLabelEquiv (α,A) :=
      pairedLabelEquiv.apply_symm_apply _
    simpa only [hlabel, thetaCandidate] using hq
  exact FCP.BFSSFermionF3C2.thetaCandidate_upstream_irreducible W hOld

/-- A SECOND exact pinned AlgebraData 2, keeping the qualified original intact. -/
noncomputable def pairedAlgebraData : AlgebraData 2 where
  color := concreteAlgebraData.color
  color_hermitian := concreteAlgebraData.color_hermitian
  color_traceless := concreteAlgebraData.color_traceless
  color_orthonormal := concreteAlgebraData.color_orthonormal
  color_spanning := concreteAlgebraData.color_spanning
  gamma := concreteAlgebraData.gamma
  gamma_symmetric := concreteAlgebraData.gamma_symmetric
  gamma_clifford := concreteAlgebraData.gamma_clifford
  theta := pairedTheta
  theta_selfAdjoint := pairedTheta_selfAdjoint
  theta_CAR := by
    intro α β A B
    have h := pairedTheta_CAR α β A B
    by_cases he : α = β ∧ A = B
    · simpa only [_root_.ite_eq_left he, one_smul] using h
    · simpa only [_root_.ite_eq_right he, ← Nat.cast_smul_eq_nsmul ℂ,
        Nat.cast_zero] using h
  theta_irreducible := pairedTheta_irreducible

theorem pairedAlgebraData_color (A : ColorIndex 2) :
    pairedAlgebraData.color A = concreteAlgebraData.color A := rfl

theorem pairedAlgebraData_gamma (i : SpaceIndex) :
    pairedAlgebraData.gamma i = concreteAlgebraData.gamma i := rfl

theorem pairedAlgebraData_theta (α : SpinIndex) (A : ColorIndex 2) :
    pairedAlgebraData.theta α A = pairedTheta α A := rfl

#print axioms pairedLabel_even
#print axioms pairedLabel_odd
#print axioms pairedTheta_even
#print axioms pairedTheta_odd
#print axioms pairedTheta_selfAdjoint
#print axioms pairedTheta_CAR
#print axioms pairedTheta_irreducible
#print axioms pairedAlgebraData
#print axioms pairedAlgebraData_color
#print axioms pairedAlgebraData_gamma
#print axioms pairedAlgebraData_theta

end
end FCP.BFSSSU2GaugeG1A
