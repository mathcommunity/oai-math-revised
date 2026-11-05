import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2FermionF3B9FiniteReachabilityProbe

/-!
# BFSS fermions F3-C1 — concrete theta-invariant submodule dichotomy

Kernel-accepted F3-B5 expands every vector in the actual 24-mode
transported Fock basis; F3-B6 extracts one ket from any nonzero invariant
submodule; F3-B9 generates all occupation kets from one.
The resulting top-or-bottom criterion is *not yet* the upstream
AlgebraData.theta_irreducible interface theorem.
-/

namespace FCP.BFSSFermionF3C1
noncomputable section

open FCP.BFSSFermionF2 FCP.BFSSFermionF3B2
open FCP.BFSSFermionF3B5 FCP.BFSSFermionF3B6
open FCP.BFSSFermionF3B9
open scoped BigOperators

private abbrev BFSSFermion := OAI.BFSSQuantum.Fermion 2

/-- The actual transported occupation basis spans any submodule that
contains every occupation ket. -/
private theorem eq_top_of_all_occupationKet
    (W : Submodule ℂ BFSSFermion)
    (hall : ∀ B : Finset (Fin 24), occupationKet B ∈ W) :
    W = ⊤ := by
  apply top_unique
  intro y _
  rw [occupationExpansion y]
  apply W.sum_mem
  intro B _
  exact W.smul_mem _ (hall B)

/-- A theta-invariant submodule containing a nonzero BFSS fermion
vector is the whole concrete 24-mode fermion space. -/
theorem thetaInvariant_eq_top_of_nonzero
    (W : Submodule ℂ BFSSFermion)
    (hθ : ∀ α A, ∀ w ∈ W, thetaCandidate α A w ∈ W)
    (x : BFSSFermion) (hxW : x ∈ W) (hx0 : x ≠ 0) :
    W = ⊤ := by
  obtain ⟨A, hA⟩ := thetaInvariant_contains_occupationKet W hθ x hxW hx0
  have hall : ∀ B : Finset (Fin 24), occupationKet B ∈ W :=
    thetaInvariant_all_occupationKet_of_one W hθ A hA
  exact eq_top_of_all_occupationKet W hall

/-- Every submodule stable under the actual theta candidates is either
zero or the entire fermion space. This is the concrete F3 dichotomy,
prior to linking the exact upstream irreducibility API. -/
theorem thetaInvariant_bot_or_top
    (W : Submodule ℂ BFSSFermion)
    (hθ : ∀ α A, ∀ w ∈ W, thetaCandidate α A w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    have hex : ∃ x : BFSSFermion, x ∈ W ∧ x ≠ 0 := by
      by_contra hnone
      have hwzero (x : BFSSFermion) (hx : x ∈ W) : x = 0 := by
        by_contra hx0
        exact hnone ⟨x, hx, hx0⟩
      apply hbot
      apply le_antisymm
      · intro x hx
        simpa [hwzero x hx]
      · exact bot_le
    obtain ⟨x, hxW, hx0⟩ := hex
    exact thetaInvariant_eq_top_of_nonzero W hθ x hxW hx0

#print axioms thetaInvariant_eq_top_of_nonzero
#print axioms thetaInvariant_bot_or_top

end
end FCP.BFSSFermionF3C1
