import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2FermionF3B5CoordinateProbe

/-! BFSS F3-B6: theta-stable selectors, nonzero coordinates, and ket extraction.
No all-ket reachability or irreducibility claim. -/
namespace FCP.BFSSFermionF3B6
noncomputable section
open FCP.BFSSFermionF1 FCP.BFSSFermionF2
open FCP.BFSSFermionF3B1 FCP.BFSSFermionF3B2
open FCP.BFSSFermionF3B4 FCP.BFSSFermionF3B5
open scoped BigOperators
private abbrev BFSSFermion := OAI.BFSSQuantum.Fermion 2

theorem thetaInvariant_occupationSelector
    (W : Submodule ℂ BFSSFermion)
    (hθ : ∀ α A, ∀ w ∈ W, thetaCandidate α A w ∈ W) :
    ∀ A : Finset (Fin 24), ∀ w ∈ W, occupationSelector A w ∈ W := by
  have hocc := thetaInvariant_occupiedMode W hθ
  have hvac := thetaInvariant_vacantMode W hθ
  have hstep (A : Finset (Fin 24)) (i : Fin 24)
      (w : BFSSFermion) (hw : w ∈ W) : step A i w ∈ W := by
    by_cases hi : i ∈ A
    · simpa only [step, _root_.ite_eq_left hi] using hocc i w hw
    · simpa only [step, _root_.ite_eq_right hi] using hvac i w hw
  have hseq (A : Finset (Fin 24)) (is : List (Fin 24)) :
      ∀ w ∈ W, selectorSeq A is w ∈ W := by
    induction is with
    | nil =>
        intro w hw
        change w ∈ W
        exact hw
    | cons i is ih =>
        intro w hw
        change step A i (selectorSeq A is w) ∈ W
        exact hstep A i _ (ih w hw)
  intro A w hw
  change selectorSeq A (Finset.univ : Finset (Fin 24)).toList w ∈ W
  exact hseq A _ w hw

theorem exists_nonzero_occupationCoeff (x : BFSSFermion) (hx : x ≠ 0) :
    ∃ A : Finset (Fin 24), occupationCoeff x A ≠ 0 := by
  by_contra hnone
  have hall (A : Finset (Fin 24)) : occupationCoeff x A = 0 := by
    by_contra ha
    exact hnone ⟨A, ha⟩
  have hsum :
      (∑ B : Finset (Fin 24), occupationCoeff x B • occupationKet B) = 0 := by
    apply Finset.sum_eq_zero
    intro B _
    rw [hall B, zero_smul]
  exact hx ((occupationExpansion x).trans hsum)

theorem thetaInvariant_contains_occupationKet
    (W : Submodule ℂ BFSSFermion)
    (hθ : ∀ α A, ∀ w ∈ W, thetaCandidate α A w ∈ W)
    (x : BFSSFermion) (hw : x ∈ W) (hx : x ≠ 0) :
    ∃ A : Finset (Fin 24), occupationKet A ∈ W := by
  obtain ⟨A, hc⟩ := exists_nonzero_occupationCoeff x hx
  have hsel : occupationSelector A x ∈ W :=
    thetaInvariant_occupationSelector W hθ A x hw
  rw [occupationSelector_apply A x] at hsel
  have hs := W.smul_mem (occupationCoeff x A)⁻¹ hsel
  have hi : (occupationCoeff x A)⁻¹ * occupationCoeff x A = 1 :=
    inv_mul_cancel₀ hc
  refine ⟨A, ?_⟩
  simpa only [smul_smul, hi, one_smul] using hs

#print axioms thetaInvariant_occupationSelector
#print axioms exists_nonzero_occupationCoeff
#print axioms thetaInvariant_contains_occupationKet
end
end FCP.BFSSFermionF3B6
