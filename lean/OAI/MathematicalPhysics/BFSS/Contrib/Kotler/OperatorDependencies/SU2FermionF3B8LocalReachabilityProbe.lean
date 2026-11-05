import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2FermionF3B7SignedModeProbe

/-!
# BFSS fermions F3-B8 — one-mode reachability in theta-invariant submodules

The accepted F3-A2 creator/annihilator stability, combined with the
actual signed and nonzero F3-B7 Fock transition coefficients, implies
closure under inserting or erasing a single occupation label.

This is local reachability only. Full finite reachability, irreducibility,
and AlgebraData 2 remain separate proof obligations.
-/

namespace FCP.BFSSFermionF3B8
noncomputable section

open FCP.BFSSFermionF1 FCP.BFSSFermionF2
open FCP.BFSSFermionF3A2 FCP.BFSSFermionF3B2
open FCP.BFSSFermionF3B7
open OAI.ContinuumCoulomb.HubbardGlobal

private abbrev BFSSFermion := OAI.BFSSQuantum.Fermion 2

/-- Any theta-stable submodule containing a canonical occupation ket also
contains the ket after inserting one previously unoccupied mode. The
genuine exterior coefficient is canceled using its proven nonzero value. -/
theorem thetaInvariant_insert_occupationKet
    (W : Submodule ℂ BFSSFermion)
    (hθ : ∀ α A, ∀ w ∈ W, thetaCandidate α A w ∈ W)
    (A : Finset (Fin 24)) (hw : occupationKet A ∈ W)
    (i : Fin 24) (hi : i ∉ A) :
    occupationKet (insert i A) ∈ W := by
  have hact : creator i (occupationKet A) ∈ W :=
    (thetaInvariant_creator_annihilator W hθ).1 i (occupationKet A) hw
  rw [creator_occupationKet i A] at hact
  have hscaled := W.smul_mem (creationCoefficient i A)⁻¹ hact
  have hc : creationCoefficient i A ≠ 0 :=
    creationCoefficient_ne_zero_of_not_mem i A hi
  have hinv : (creationCoefficient i A)⁻¹ * creationCoefficient i A = 1 :=
    inv_mul_cancel₀ hc
  simpa only [smul_smul, hinv, one_smul] using hscaled

/-- Removing any occupied mode from a canonical occupation ket preserves
membership in a theta-stable submodule, with exact signed coefficient. -/
theorem thetaInvariant_erase_occupationKet
    (W : Submodule ℂ BFSSFermion)
    (hθ : ∀ α A, ∀ w ∈ W, thetaCandidate α A w ∈ W)
    (A : Finset (Fin 24)) (hw : occupationKet A ∈ W)
    (i : Fin 24) (hi : i ∈ A) :
    occupationKet (A.erase i) ∈ W := by
  have hact : annihilator i (occupationKet A) ∈ W :=
    (thetaInvariant_creator_annihilator W hθ).2 i (occupationKet A) hw
  rw [annihilator_occupationKet_of_mem i A hi] at hact
  have hscaled := W.smul_mem (creationCoefficient i (A.erase i))⁻¹ hact
  have hc : creationCoefficient i (A.erase i) ≠ 0 :=
    annihilationCoefficient_ne_zero_of_mem i A hi
  have hinv : (creationCoefficient i (A.erase i))⁻¹ *
      creationCoefficient i (A.erase i) = 1 :=
    inv_mul_cancel₀ hc
  simpa only [smul_smul, hinv, one_smul] using hscaled

#print axioms thetaInvariant_insert_occupationKet
#print axioms thetaInvariant_erase_occupationKet

end
end FCP.BFSSFermionF3B8
