import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2FermionF3B1OccupationProbe

/-!
# BFSS fermions F3-B2 — actual occupation-basis mode action

Following kernel-accepted Gate #61, identify each transported mode-number
operator with the pinned upstream Fock number operator and prove its exact
zero-or-one action on the 24-mode occupation basis, transported into the
unchanged BFSS Fermion 2 Hilbert space by the accepted F1 unitary.

This module does not prove coordinate isolation or irreducibility.
-/

namespace FCP.BFSSFermionF3B2
noncomputable section

open FCP.BFSSFermionF1 FCP.BFSSFermionF2 FCP.BFSSFermionF3B1
open OAI.Laughlin.Fock OAI.ContinuumCoulomb.HubbardGlobal

private abbrev BFSSFermion := OAI.BFSSQuantum.Fermion 2
private abbrev BFSSOp := BFSSFermion →L[ℂ] BFSSFermion

/-- The existing canonical exterior-algebra occupation basis, transported
through exactly the accepted F1 coordinate equivalence and Hilbert unitary. -/
noncomputable def occupationKet (A : Finset (Fin 24)) : BFSSFermion :=
  fockBFSSUnitary (fockCoordinates 23 (fockBasis 23 A))

/-- The accepted F3-B1 occupied-mode operator is precisely the conjugate of
the pinned Hubbard number operator in the accepted F1 Fock realization. -/
theorem occupiedMode_as_fockNumber (i : Fin 24) :
    occupiedMode i = onBFSS (fockOperator (number i)) := by
  have hnum : fockOperator (number i) =
      fockOperator (create i) * fockOperator (annihilate i) := by
    simp only [number, transfer, fockOperator_mul, ContinuousLinearMap.mul_def]
  calc
    occupiedMode i =
        onBFSS (fockOperator (create i)) *
          onBFSS (fockOperator (annihilate i)) := rfl
    _ = onBFSS (fockOperator (create i) * fockOperator (annihilate i)) := by
      exact (map_mul fockBFSSUnitary.conjStarAlgEquiv _ _).symm
    _ = onBFSS (fockOperator (number i)) := by rw [hnum]

/-- Genuine occupancy eigenvalue action on each actual transported basis
vector, for every mode including all spectator occupations. -/
theorem occupiedMode_occupationKet (i : Fin 24) (A : Finset (Fin 24)) :
    occupiedMode i (occupationKet A) =
      if i ∈ A then occupationKet A else 0 := by
  calc
    occupiedMode i (occupationKet A) =
        fockBFSSUnitary
          (fockOperator (number i) (fockCoordinates 23 (fockBasis 23 A))) := by
      rw [occupiedMode_as_fockNumber]
      simp only [occupationKet, onBFSS,
        LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
        LinearIsometryEquiv.symm_apply_apply]
    _ = fockBFSSUnitary (fockCoordinates 23 (number i (fockBasis 23 A))) := by
      rw [fockOperator_coordinates]
    _ = if i ∈ A then occupationKet A else 0 := by
      rw [number_basis]
      by_cases hi : i ∈ A
      · simp [hi, occupationKet]
      · simp [hi, occupationKet]

/-- The complementary transported mode operator has the opposite
zero-or-one action on the actual occupation basis. -/
theorem vacantMode_occupationKet (i : Fin 24) (A : Finset (Fin 24)) :
    vacantMode i (occupationKet A) =
      if i ∈ A then 0 else occupationKet A := by
  by_cases hi : i ∈ A
  · simp [vacantMode, occupiedMode_occupationKet, hi]
  · simp [vacantMode, occupiedMode_occupationKet, hi]

#print axioms occupiedMode_as_fockNumber
#print axioms occupiedMode_occupationKet
#print axioms vacantMode_occupationKet

end
end FCP.BFSSFermionF3B2
