import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K9ASourceChargeCoefficientCrosswalkProbe

/-!
# BFSS SU(2) G4-K9B: source pair crosswalk and conditional core equivalence
UNCOMPILED candidate. Conditional results below assume the potential
multiplier identity as an EXPLICIT hypothesis. They do not prove it.
-/

namespace FCP.BFSSSU2GaugeG4K9B
noncomputable section
open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open Finset
open FCP.BFSSSU2GaugeG4K9A

/-- Original pair and ordered spatial color brackets literally coincide on i<j. -/
theorem sourceCoordinateBracketUpperPair
    {N : ℕ} (M : AlgebraData N) (x : Boson N)
    (p : BFSSGamma.SpatialPair) (A : ColorIndex N) :
    M.coordinateBracket x p A =
      M.coordinateBracketAll x p.1.1 p.1.2 A := by
  rfl

/-- Original gammaTwo agrees with original pairGamma at i<j. -/
theorem sourceGammaTwoUpperPair
    {N : ℕ} (M : AlgebraData N) (p : BFSSGamma.SpatialPair) :
    M.gammaTwo p.1.1 p.1.2 =
      BFSSGamma.pairGamma M.gamma p := by
  change BFSSGamma.gammaTwo M.gamma p.1.1 p.1.2 = _
  rw [BFSSGamma.gammaTwo_alt M.gamma M.gamma_clifford]
  simp [BFSSGamma.pairGamma, p.2.ne]

/-- Qualified G4-K9A coefficient in the original upper-triangle notation. -/
theorem sourceMasslessCoefficient_eq_originalUpperTriangle
    {N : ℕ} (M : AlgebraData N) (x : Boson N)
    (α β : SpinIndex) (A : ColorIndex N) :
    M.deformedPotentialCoefficients 1 0 x α (β, A) =
      ∑ p : BFSSGamma.SpatialPair,
        M.coordinateBracketAll x p.1.1 p.1.2 A *
          M.gammaTwo p.1.1 p.1.2 α β := by
  rw [sourceMasslessPotentialCoefficient_eq_pairSum M x α β A]
  apply Finset.sum_congr rfl
  intro p _
  rw [← sourceCoordinateBracketUpperPair M x p A]
  rw [sourceGammaTwoUpperPair M p]

/-- The source kinetic terms cancel exactly in the charge difference. -/
theorem sourceChargeDifference_eq_potentialDifference
    {N : ℕ} (M : AlgebraData N) (α : SpinIndex)
    (f : SmoothCore N) (x : Boson N) :
    M.deformedCoreCharge 1 0 α f x - M.charge α f x =
      M.deformedPotentialMultiplier 1 0 x α (f x) -
        M.bracketMultiplier α x (f x) := by
  rw [M.deformedCoreCharge_apply, M.charge_kinetic_plus_bracket]
  abel

/-- Fully source-typed charge identity from an OPEN explicit multiplier premise. -/
theorem sourceCharge_eq_of_potentialAgreement
    {N : ℕ} (M : AlgebraData N) (α : SpinIndex)
    (hp : ∀ x : Boson N,
      M.deformedPotentialMultiplier 1 0 x α = M.bracketMultiplier α x)
    (f : SmoothCore N) :
    M.deformedCoreCharge 1 0 α f = M.charge α f := by
  apply DFunLike.ext
  intro x
  rw [M.deformedCoreCharge_apply, M.charge_kinetic_plus_bracket, hp x]

/-- Source quadratic forms agree IF the pointwise multiplier identity holds. -/
theorem sourceCoreForm_eq_of_potentialAgreement
    {N : ℕ} (M : AlgebraData N)
    (hp : ∀ (α : SpinIndex) (x : Boson N),
      M.deformedPotentialMultiplier 1 0 x α = M.bracketMultiplier α x)
    (f : SmoothCore N) :
    M.deformedCoreEnergy 1 0 f = M.coreForm f := by
  change (1 / 16 : ℝ) * (∑ α : SpinIndex,
    ‖coreToL2 (M.deformedCoreCharge 1 0 α f)‖ ^ 2) =
      (1 / 16 : ℝ) * (∑ α : SpinIndex,
        ‖coreToL2 (M.charge α f)‖ ^ 2)
  congr 1
  apply Finset.sum_congr rfl
  intro α _
  rw [sourceCharge_eq_of_potentialAgreement M α (hp α) f]

#print axioms sourceCoordinateBracketUpperPair
#print axioms sourceGammaTwoUpperPair
#print axioms sourceMasslessCoefficient_eq_originalUpperTriangle
#print axioms sourceChargeDifference_eq_potentialDifference
#print axioms sourceCharge_eq_of_potentialAgreement
#print axioms sourceCoreForm_eq_of_potentialAgreement

end
end FCP.BFSSSU2GaugeG4K9B
