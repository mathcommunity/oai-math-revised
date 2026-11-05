import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2FermionF3B6NonzeroKetProbe

/-!
# BFSS fermions F3-B7 — signed single-mode transitions of actual occupation kets

Transport the pinned upstream exact exterior Fock basis action along F1.
The creation and annihilation coefficients retain their genuine exterior
permutation signs. Reachability of all 2^24 kets is a separate obligation.
-/

namespace FCP.BFSSFermionF3B7
noncomputable section

open FCP.BFSSFermionF1 FCP.BFSSFermionF3B2
open OAI.Laughlin.Fock OAI.ContinuumCoulomb.HubbardGlobal

/-- The actual transported creator acts on a canonical occupation ket
with the exact upstream exterior permutation coefficient. -/
theorem creator_occupationKet (i : Fin 24) (A : Finset (Fin 24)) :
    creator i (occupationKet A) =
      creationCoefficient i A • occupationKet (insert i A) := by
  calc
    creator i (occupationKet A) =
        fockBFSSUnitary
          (fockOperator (create i) (fockCoordinates 23 (fockBasis 23 A))) := by
      simp only [creator, occupationKet, onBFSS,
        LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
        LinearIsometryEquiv.symm_apply_apply]
    _ = fockBFSSUnitary (fockCoordinates 23 (create i (fockBasis 23 A))) := by
      rw [fockOperator_coordinates]
    _ = creationCoefficient i A • occupationKet (insert i A) := by
      rw [create_basis]
      simp only [map_smul, occupationKet]

/-- A transported annihilator removes an occupied mode with the exact
signed upstream coefficient. -/
theorem annihilator_occupationKet_of_mem
    (i : Fin 24) (A : Finset (Fin 24)) (hi : i ∈ A) :
    annihilator i (occupationKet A) =
      creationCoefficient i (A.erase i) • occupationKet (A.erase i) := by
  calc
    annihilator i (occupationKet A) =
        fockBFSSUnitary
          (fockOperator (annihilate i) (fockCoordinates 23 (fockBasis 23 A))) := by
      simp only [annihilator, occupationKet, onBFSS,
        LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
        LinearIsometryEquiv.symm_apply_apply]
    _ = fockBFSSUnitary (fockCoordinates 23 (annihilate i (fockBasis 23 A))) := by
      rw [fockOperator_coordinates]
    _ = creationCoefficient i (A.erase i) • occupationKet (A.erase i) := by
      rw [annihilate_occupied_basis i A hi]
      simp only [map_smul, occupationKet]

/-- The upstream exterior coefficient is ±1 for every unoccupied mode,
hence always invertible in the exact complex scalar field. -/
theorem creationCoefficient_ne_zero_of_not_mem
    (i : Fin 24) (A : Finset (Fin 24)) (hi : i ∉ A) :
    creationCoefficient i A ≠ 0 := by
  rcases creationCoefficient_signed i A hi with h | h
  · simp [h]
  · simp [h]

/-- Removing an occupied mode likewise has a nonzero transition coefficient. -/
theorem annihilationCoefficient_ne_zero_of_mem
    (i : Fin 24) (A : Finset (Fin 24)) (hi : i ∈ A) :
    creationCoefficient i (A.erase i) ≠ 0 :=
  creationCoefficient_ne_zero_of_not_mem i (A.erase i) (Finset.notMem_erase _ _)

#print axioms creator_occupationKet
#print axioms annihilator_occupationKet_of_mem
#print axioms creationCoefficient_ne_zero_of_not_mem
#print axioms annihilationCoefficient_ne_zero_of_mem

end
end FCP.BFSSFermionF3B7
