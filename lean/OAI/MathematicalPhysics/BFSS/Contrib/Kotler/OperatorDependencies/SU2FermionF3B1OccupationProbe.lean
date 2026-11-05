import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2FermionF3RecoveryProbe

/-!
# BFSS fermions F3-B1 — theta-stable mode-occupation operators

Building on kernel-accepted F3-A2 (Gate #60), define the transported
creator-annihilator mode-number operator and its complement, and show
theta-invariant submodules are stable under both.

This step DOES NOT show the operators act as occupation-basis projections.
Diagonal action on canonical Fock basis vectors, nonzero-coordinate isolation,
basis generation and irreducibility remain unproved future obligations.
-/

namespace FCP.BFSSFermionF3B1
noncomputable section

open FCP.BFSSFermionF1 FCP.BFSSFermionF2 FCP.BFSSFermionF3A2

private abbrev BFSSFermion := OAI.BFSSQuantum.Fermion 2
private abbrev BFSSOp := BFSSFermion →L[ℂ] BFSSFermion

/-- The transported creation-after-annihilation mode operator. Its
occupation-basis diagonal action is a separate, still-pending theorem. -/
noncomputable def occupiedMode (i : Fin 24) : BFSSOp :=
  creator i * annihilator i

/-- Complementary mode operator. Its projector semantics are not assumed. -/
noncomputable def vacantMode (i : Fin 24) : BFSSOp :=
  1 - occupiedMode i

/-- Theta invariance implies stability under every creator-after-annihilator
operator, without any occupation-basis or irreducibility assumption. -/
theorem thetaInvariant_occupiedMode
    (W : Submodule ℂ BFSSFermion)
    (hθ : ∀ α A, ∀ w ∈ W, thetaCandidate α A w ∈ W) :
    ∀ i : Fin 24, ∀ w ∈ W, occupiedMode i w ∈ W := by
  intro i w hw
  have h := thetaInvariant_creator_annihilator W hθ
  change creator i (annihilator i w) ∈ W
  exact h.1 i (annihilator i w) (h.2 i w hw)

/-- Theta invariance also implies stability under identity minus the
mode operator; this uses only submodule subtraction closure. -/
theorem thetaInvariant_vacantMode
    (W : Submodule ℂ BFSSFermion)
    (hθ : ∀ α A, ∀ w ∈ W, thetaCandidate α A w ∈ W) :
    ∀ i : Fin 24, ∀ w ∈ W, vacantMode i w ∈ W := by
  intro i w hw
  have hn := thetaInvariant_occupiedMode W hθ i w hw
  have hsub := W.sub_mem hw hn
  simpa [vacantMode] using hsub

#print axioms thetaInvariant_occupiedMode
#print axioms thetaInvariant_vacantMode

end
end FCP.BFSSFermionF3B1
