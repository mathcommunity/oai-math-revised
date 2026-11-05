import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4GMajoranaModeCovarianceProbe

/-!
# BFSS SU(2) G4-H — exact paired 48-theta fermion adjoint covariance

This stage turns the accepted real/imaginary 24-mode Majorana laws
into the literal upstream AlgebraData.GaugeData.fermion_adjoint
obligation for the accepted pairedAlgebraData : AlgebraData 2 and
G4-E fermionGaugeUnitaryHom on Fermion 2.

The pairing is the explicit G1-A spinPairEquiv/colorModeEquiv.
The input color is A, the output color is B, and no off-block
spin-pair terms survive the exact G3-C one-particle matrix law.

Fermionic joint continuity and the full GaugeData remain open.
-/

namespace FCP.BFSSSU2GaugeG4H
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open FCP.BFSSFermionF1 FCP.BFSSFermionF2
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG3A FCP.BFSSSU2GaugeG3C
open FCP.BFSSSU2GaugeG4B FCP.BFSSSU2GaugeG4E
open FCP.BFSSSU2GaugeG4G

/-- Every 24-mode covariance sum is exactly one three-color block,
with all seven other spin-pair blocks proven to contribute zero.
The result is independent of which Majorana component supplies X. -/
theorem complexOneParticleMatrix_paired_block_sum
    (g : GaugeGroup 2) (j : Fin 8) (A : ColorIndex 2)
    (X : Fin 24 → Fermion 2) :
    (∑ m : Fin 24,
      complexOneParticleMatrix g m (colorModeEquiv (j,A)) • X m) =
    ∑ B : ColorIndex 2,
      (adjointColorMatrix g B A : ℂ) • X (colorModeEquiv (j,B)) := by
  classical
  calc
    _ = ∑ p : Fin 8 × ColorIndex 2,
          complexOneParticleMatrix g (colorModeEquiv p)
            (colorModeEquiv (j,A)) • X (colorModeEquiv p) :=
        (Equiv.sum_comp colorModeEquiv _).symm
    _ = ∑ k : Fin 8, ∑ B : ColorIndex 2,
          (if k = j then (adjointColorMatrix g B A : ℂ) else 0) •
            X (colorModeEquiv (k,B)) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro B _
        rw [complexOneParticleMatrix_block]
    _ = ∑ k : Fin 8,
          if k = j then
            ∑ B : ColorIndex 2,
              (adjointColorMatrix g B A : ℂ) • X (colorModeEquiv (k,B))
          else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k = j
        · simp [hk]
        · simp [hk]
    _ = ∑ B : ColorIndex 2,
          (adjointColorMatrix g B A : ℂ) • X (colorModeEquiv (j,B)) := by
        simp

/-- Exact even spin-pair/theta field, not an independently chosen
Majorana or surrogate fermionic representation. -/
theorem pairedTheta_even_fermionGauge_covariant
    (g : GaugeGroup 2) (j : Fin 8) (A : ColorIndex 2)
    (v : Fermion 2) :
    fermionGaugeUnitaryHom g
      (pairedAlgebraData.theta (spinPairEquiv.symm (j,(0 : Fin 2))) A v) =
    ∑ B : ColorIndex 2,
      (pairedAlgebraData.adjointCoefficient g A B : ℂ) •
        pairedAlgebraData.theta (spinPairEquiv.symm (j,(0 : Fin 2))) B
          (fermionGaugeUnitaryHom g v) := by
  change
    fermionGaugeLinearEquiv g
      (pairedTheta (spinPairEquiv.symm (j,(0 : Fin 2))) A v) =
    ∑ B : ColorIndex 2,
      (pairedAlgebraData.adjointCoefficient g A B : ℂ) •
        pairedTheta (spinPairEquiv.symm (j,(0 : Fin 2))) B
          (fermionGaugeLinearEquiv g v)
  simp_rw [pairedTheta_even]
  rw [majorana0_fermionGauge_covariant]
  simpa only [adjointColorMatrix] using
    (complexOneParticleMatrix_paired_block_sum g j A
      (fun m => majorana0 m (fermionGaugeLinearEquiv g v)))

/-- Exact odd spin-pair/theta covariance including the imaginary
Majorana phase; the SU(2) coefficients are real. -/
theorem pairedTheta_odd_fermionGauge_covariant
    (g : GaugeGroup 2) (j : Fin 8) (A : ColorIndex 2)
    (v : Fermion 2) :
    fermionGaugeUnitaryHom g
      (pairedAlgebraData.theta (spinPairEquiv.symm (j,(1 : Fin 2))) A v) =
    ∑ B : ColorIndex 2,
      (pairedAlgebraData.adjointCoefficient g A B : ℂ) •
        pairedAlgebraData.theta (spinPairEquiv.symm (j,(1 : Fin 2))) B
          (fermionGaugeUnitaryHom g v) := by
  change
    fermionGaugeLinearEquiv g
      (pairedTheta (spinPairEquiv.symm (j,(1 : Fin 2))) A v) =
    ∑ B : ColorIndex 2,
      (pairedAlgebraData.adjointCoefficient g A B : ℂ) •
        pairedTheta (spinPairEquiv.symm (j,(1 : Fin 2))) B
          (fermionGaugeLinearEquiv g v)
  simp_rw [pairedTheta_odd]
  rw [majorana1_fermionGauge_covariant]
  simpa only [adjointColorMatrix] using
    (complexOneParticleMatrix_paired_block_sum g j A
      (fun m => majorana1 m (fermionGaugeLinearEquiv g v)))

/-- The exact literal pinned GaugeData.fermion_adjoint equation,
for every one of the 16 spin labels, all three colors and all states. -/
theorem pairedAlgebraData_fermion_adjoint
    (g : GaugeGroup 2) (α : SpinIndex)
    (A : ColorIndex 2) (v : Fermion 2) :
    fermionGaugeUnitaryHom g (pairedAlgebraData.theta α A v) =
    ∑ B : ColorIndex 2,
      (pairedAlgebraData.adjointCoefficient g A B : ℂ) •
        pairedAlgebraData.theta α B (fermionGaugeUnitaryHom g v) := by
  rcases hp : spinPairEquiv α with ⟨j,r⟩
  have hα : α = spinPairEquiv.symm (j,r) := by
    apply spinPairEquiv.injective
    simpa only [spinPairEquiv.apply_symm_apply] using hp
  fin_cases r
  · rw [hα]
    exact pairedTheta_even_fermionGauge_covariant g j A v
  · rw [hα]
    exact pairedTheta_odd_fermionGauge_covariant g j A v

/-- Type-check the equation against the entire upstream field
signature, not only individual concrete mode identities. -/
theorem fermion_adjoint_exact_field :
    ∀ (g : GaugeGroup 2) (α : SpinIndex)
      (A : ColorIndex 2) (v : Fermion 2),
      fermionGaugeUnitaryHom g (pairedAlgebraData.theta α A v) =
        ∑ B : ColorIndex 2,
          (pairedAlgebraData.adjointCoefficient g A B : ℂ) •
            pairedAlgebraData.theta α B (fermionGaugeUnitaryHom g v) :=
  pairedAlgebraData_fermion_adjoint

#print axioms complexOneParticleMatrix_paired_block_sum
#print axioms pairedTheta_even_fermionGauge_covariant
#print axioms pairedTheta_odd_fermionGauge_covariant
#print axioms pairedAlgebraData_fermion_adjoint
#print axioms fermion_adjoint_exact_field

end
end FCP.BFSSSU2GaugeG4H
