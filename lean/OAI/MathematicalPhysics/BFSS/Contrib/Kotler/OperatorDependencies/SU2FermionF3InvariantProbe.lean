import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2FermionF2B2ThetaProbe

/-!
# BFSS fermions F3-A1 — invariant-submodule index transport

F2-B2d2 is now kernel accepted. Irreducibility is a separate theorem:
a complex submodule of the pinned BFSS Fermion 2 Hilbert space invariant
under every thetaCandidate must be bottom or top.

This first F3 step proves precisely that invariance under all BFSS
spin/color theta labels is equivalent to invariance under all 48
Majorana product labels, via the existing thetaLabelEquiv.

Neither direction proves that any invariant submodule is trivial.
Creation/annihilation recovery and Fock occupation-basis generation
remain subsequent, separately checked obligations.
-/

namespace FCP.BFSSFermionF3
noncomputable section

open FCP.BFSSFermionF1 FCP.BFSSFermionF2

private abbrev BFSSFermion := OAI.BFSSQuantum.Fermion 2

/-- Any submodule invariant under the exact BFSS thetaCandidate labels
is invariant under an arbitrary one of the 48 Majorana generators. -/
theorem thetaInvariant_majoranaCandidate
    (W : Submodule ℂ BFSSFermion)
    (hθ : ∀ α A, ∀ w ∈ W, thetaCandidate α A w ∈ W)
    (p : Fin 24 × Fin 2) (w : BFSSFermion) (hw : w ∈ W) :
    majoranaCandidate p w ∈ W := by
  obtain ⟨⟨α, A⟩, hlabel⟩ := thetaLabelEquiv.surjective p
  have h := hθ α A w hw
  change majoranaCandidate (thetaLabelEquiv (α, A)) w ∈ W at h
  simpa only [hlabel] using h

/-- A submodule is theta-invariant precisely when it is invariant
under the 48-generator family, on the exact pinned fermion type. -/
theorem thetaInvariant_iff_majoranaCandidate (W : Submodule ℂ BFSSFermion) :
    (∀ α A, ∀ w ∈ W, thetaCandidate α A w ∈ W) ↔
      (∀ p : Fin 24 × Fin 2, ∀ w ∈ W, majoranaCandidate p w ∈ W) := by
  constructor
  · intro hθ p w hw
    exact thetaInvariant_majoranaCandidate W hθ p w hw
  · intro hm α A w hw
    exact hm (thetaLabelEquiv (α, A)) w hw

/-- Invariance under all theta labels also implies invariance under
each real and each imaginary Majorana, for every Fock mode. -/
theorem thetaInvariant_majoranaComponents (W : Submodule ℂ BFSSFermion)
    (hθ : ∀ α A, ∀ w ∈ W, thetaCandidate α A w ∈ W) :
    (∀ i : Fin 24, ∀ w ∈ W, majorana0 i w ∈ W) ∧
      (∀ i : Fin 24, ∀ w ∈ W, majorana1 i w ∈ W) := by
  constructor
  · intro i w hw
    have h := thetaInvariant_majoranaCandidate W hθ (i, 0) w hw
    simpa [majoranaCandidate] using h
  · intro i w hw
    have h := thetaInvariant_majoranaCandidate W hθ (i, 1) w hw
    simpa [majoranaCandidate] using h

#print axioms thetaInvariant_majoranaCandidate
#print axioms thetaInvariant_iff_majoranaCandidate
#print axioms thetaInvariant_majoranaComponents

end
end FCP.BFSSFermionF3
