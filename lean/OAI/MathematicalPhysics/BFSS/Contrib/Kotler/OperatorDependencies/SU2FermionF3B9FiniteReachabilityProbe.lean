import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2FermionF3B8LocalReachabilityProbe

/-!
# BFSS fermions F3-B9 — all occupation kets mutually reachable

From accepted one-mode theta-stable insert/erase transitions, induct
over occupation Finsets. This proves full finite 24-mode ket
reachability inside theta-invariant submodules, not yet irreducibility.
-/

namespace FCP.BFSSFermionF3B9
noncomputable section

open FCP.BFSSFermionF2 FCP.BFSSFermionF3B2
open FCP.BFSSFermionF3B8

private abbrev BFSSFermion := OAI.BFSSQuantum.Fermion 2

/-- Repeated erasure carries any occupation ket to the vacuum ket in
every theta-invariant submodule containing the starting ket. -/
theorem thetaInvariant_vacuum_of_occupationKet
    (W : Submodule ℂ BFSSFermion)
    (hθ : ∀ α A, ∀ w ∈ W, thetaCandidate α A w ∈ W) :
    ∀ A : Finset (Fin 24),
      occupationKet A ∈ W →
        occupationKet (∅ : Finset (Fin 24)) ∈ W := by
  intro A
  induction A using Finset.induction_on with
  | empty =>
      intro hw
      exact hw
  | @insert i s hi ih =>
      intro hw
      have herase : occupationKet ((insert i s).erase i) ∈ W :=
        thetaInvariant_erase_occupationKet W hθ (insert i s) hw i
          (Finset.mem_insert_self i s)
      have hs : occupationKet s ∈ W := by
        simpa only [Finset.erase_insert hi] using herase
      exact ih hs

/-- From the vacuum ket, repeated insertion reaches every target
occupation ket while preserving membership in a theta-invariant W. -/
theorem thetaInvariant_all_from_vacuum
    (W : Submodule ℂ BFSSFermion)
    (hθ : ∀ α A, ∀ w ∈ W, thetaCandidate α A w ∈ W) :
    ∀ B : Finset (Fin 24),
      occupationKet (∅ : Finset (Fin 24)) ∈ W →
        occupationKet B ∈ W := by
  intro B
  induction B using Finset.induction_on with
  | empty =>
      intro hw
      exact hw
  | @insert i s hi ih =>
      intro hw
      exact thetaInvariant_insert_occupationKet W hθ s (ih hw) i hi

/-- Genuine all-to-all reachability: one occupation ket implies all
other canonical 24-mode occupation kets belong to the same W. -/
theorem thetaInvariant_all_occupationKet_of_one
    (W : Submodule ℂ BFSSFermion)
    (hθ : ∀ α A, ∀ w ∈ W, thetaCandidate α A w ∈ W)
    (A : Finset (Fin 24)) (hA : occupationKet A ∈ W) :
    ∀ B : Finset (Fin 24), occupationKet B ∈ W := by
  have hvac : occupationKet (∅ : Finset (Fin 24)) ∈ W :=
    thetaInvariant_vacuum_of_occupationKet W hθ A hA
  intro B
  exact thetaInvariant_all_from_vacuum W hθ B hvac

#print axioms thetaInvariant_vacuum_of_occupationKet
#print axioms thetaInvariant_all_from_vacuum
#print axioms thetaInvariant_all_occupationKet_of_one

end
end FCP.BFSSFermionF3B9
