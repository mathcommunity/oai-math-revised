import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4IB2ExteriorFockTwoWedgeContinuityProbe

/-!
# BFSS SU(2) G4-I-B3 — parameter continuity for the full exterior Fock space

Use exactly the pinned `fockBasis 23`, `fockCoordinates 23` and G4-A
`exteriorGauge` with the accepted G4-I-B1 orbital continuity.

First establish the exact finite occupation-coordinate polynomial
for multiplying *any* two exterior states, then its joint continuity
after transport to the actual 2^24-dimensional normed coordinate
space. By algebraic induction over genuine wedges this proves
parameter continuity for every fixed exterior state.

No continuity is assumed on the bare algebraic exterior space.
The full joint `Fermion 2` continuity and pinned `GaugeData`
structure remain separate future obligations.
-/

namespace FCP.BFSSSU2GaugeG4IB3
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open OAI.Laughlin.Fock
open OAI.ContinuumCoulomb.HubbardGlobal
open FCP.BFSSSU2GaugeG4A FCP.BFSSSU2GaugeG4D
open FCP.BFSSSU2GaugeG4IB1

private abbrev Fock23 := Space 23
private abbrev Coordinates23 := FockCoordinateSpace 23
private abbrev Occupation := Finset (Fin 24)

/-- The exact occupation-coordinate product of two pinned exterior
basis vectors. Its signs are inherited from the genuine wedge algebra. -/
noncomputable def fockProductBasisCoordinate (A B : Occupation) :
    Coordinates23 :=
  fockCoordinates 23 (fockBasis 23 A * fockBasis 23 B)

/-- The full exterior product is a FINITE polynomial of genuine
occupation-basis coordinates; no alternative Fock multiplication. -/
theorem fockProductCoordinates_expansion (x y : Fock23) :
    fockCoordinates 23 (x * y) =
      ∑ A : Occupation, ∑ B : Occupation,
        ((fockCoordinates 23 x) A * (fockCoordinates 23 y) B) •
          fockProductBasisCoordinate A B := by
  have hx : x =
      ∑ A : Occupation, ((fockCoordinates 23 x) A) • fockBasis 23 A := by
    simpa only [fockCoordinates_apply] using ((fockBasis 23).sum_repr x).symm
  have hy : y =
      ∑ B : Occupation, ((fockCoordinates 23 y) B) • fockBasis 23 B := by
    simpa only [fockCoordinates_apply] using ((fockBasis 23).sum_repr y).symm
  calc
    fockCoordinates 23 (x * y) =
        fockCoordinates 23
          ((∑ A : Occupation, ((fockCoordinates 23 x) A) • fockBasis 23 A) *
           (∑ B : Occupation, ((fockCoordinates 23 y) B) • fockBasis 23 B)) := by
            exact congrArg (fockCoordinates 23)
              (congrArg₂ (fun a b : Fock23 => a * b) hx hy)
    _ = ∑ A : Occupation, ∑ B : Occupation,
          ((fockCoordinates 23 x) A * (fockCoordinates 23 y) B) •
            fockProductBasisCoordinate A B := by
      calc
        _ = ∑ B : Occupation, ∑ A : Occupation,
              ((fockCoordinates 23 y) B * (fockCoordinates 23 x) A) •
                fockProductBasisCoordinate A B := by
                  simp only [Finset.sum_mul, Finset.mul_sum,
                    smul_mul_assoc, mul_smul_comm, map_sum,
                    map_smul, Finset.smul_sum, smul_smul,
                    fockProductBasisCoordinate]
        _ = ∑ A : Occupation, ∑ B : Occupation,
              ((fockCoordinates 23 x) A * (fockCoordinates 23 y) B) •
                fockProductBasisCoordinate A B := by
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro A _
                  apply Finset.sum_congr rfl
                  intro B _
                  rw [mul_comm ((fockCoordinates 23 y) B)
                    ((fockCoordinates 23 x) A)]

/-- Genuine exterior multiplication transported *through* the
already pinned finite-dimensional occupation coordinate equivalence. -/
noncomputable def fockCoordinateProduct
    (p : Coordinates23 × Coordinates23) : Coordinates23 :=
  fockCoordinates 23
    ((fockCoordinates 23).symm p.1 * (fockCoordinates 23).symm p.2)

/-- The actual finite Fock-coordinate product is jointly continuous.
This does not assert the bare algebraic Space 23 carries a norm. -/
theorem fockCoordinateProduct_jointContinuous :
    Continuous fockCoordinateProduct := by
  have hexp :
      fockCoordinateProduct =
        (fun p : Coordinates23 × Coordinates23 =>
          ∑ A : Occupation, ∑ B : Occupation,
            (p.1 A * p.2 B) • fockProductBasisCoordinate A B) := by
    funext p
    unfold fockCoordinateProduct
    rw [fockProductCoordinates_expansion]
    simp only [LinearEquiv.apply_symm_apply]
  rw [hexp]
  apply continuous_finsetSum
  intro A _
  apply continuous_finsetSum
  intro B _
  exact ((((PiLp.continuous_apply 2 _ A).comp continuous_fst).mul
    ((PiLp.continuous_apply 2 _ B).comp continuous_snd)).smul
      continuous_const)

/-- Full parameter continuity of the **actual** BFSS SU(2)
exterior-Fock gauge representation on every fixed Fock vector,
in the pinned 2^24-dimensional occupation-coordinate Hilbert norm. -/
theorem exteriorGauge_allCoordinates_continuous (x : Fock23) :
    Continuous (fun g : GaugeGroup 2 =>
      fockCoordinates 23 (exteriorGauge g x)) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    have he :
        (fun g : GaugeGroup 2 =>
          fockCoordinates 23
            (exteriorGauge g (algebraMap ℂ Fock23 r))) =
        (fun _ : GaugeGroup 2 =>
          fockCoordinates 23 (algebraMap ℂ Fock23 r)) := by
            funext g
            simp only [AlgHom.commutes]
    rw [he]
    exact continuous_const
  | add x y hx hy =>
    have he :
        (fun g : GaugeGroup 2 =>
          fockCoordinates 23 (exteriorGauge g (x + y))) =
        (fun g : GaugeGroup 2 =>
          fockCoordinates 23 (exteriorGauge g x) +
            fockCoordinates 23 (exteriorGauge g y)) := by
            funext g
            simp only [map_add]
    rw [he]
    exact hx.add hy
  | ι_mul x v hx =>
    have hpair : Continuous (fun g : GaugeGroup 2 =>
        (fockCoordinates 23
            (exteriorGauge g (ExteriorAlgebra.ι ℂ v)),
         fockCoordinates 23 (exteriorGauge g x))) :=
      (exteriorGauge_seedCoordinate_continuous v).prodMk hx
    have he :
        (fun g : GaugeGroup 2 =>
          fockCoordinates 23
            (exteriorGauge g (ExteriorAlgebra.ι ℂ v * x))) =
        (fun g : GaugeGroup 2 =>
          fockCoordinateProduct
            (fockCoordinates 23 (exteriorGauge g (ExteriorAlgebra.ι ℂ v)),
             fockCoordinates 23 (exteriorGauge g x))) := by
      funext g
      change fockCoordinates 23 (exteriorGauge g (ExteriorAlgebra.ι ℂ v * x)) =
        fockCoordinates 23
          ((fockCoordinates 23).symm
              (fockCoordinates 23 (exteriorGauge g (ExteriorAlgebra.ι ℂ v))) *
           (fockCoordinates 23).symm
              (fockCoordinates 23 (exteriorGauge g x)))
      simpa only [LinearEquiv.symm_apply_apply] using
        congrArg (fockCoordinates 23)
          (map_mul (exteriorGauge g) (ExteriorAlgebra.ι ℂ v) x)
    rw [he]
    exact fockCoordinateProduct_jointContinuous.comp hpair

#print axioms fockProductBasisCoordinate
#print axioms fockProductCoordinates_expansion
#print axioms fockCoordinateProduct
#print axioms fockCoordinateProduct_jointContinuous
#print axioms exteriorGauge_allCoordinates_continuous

end
end FCP.BFSSSU2GaugeG4IB3
