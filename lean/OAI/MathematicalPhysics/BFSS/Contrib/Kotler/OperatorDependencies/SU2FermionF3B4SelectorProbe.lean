import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2FermionF3B3ProjectorProbe

/-!
# BFSS fermions F3-B4 — 24-mode occupation-label selector on basis vectors

The actual transported occupied / vacant operators are selected according to
one target occupation label. Their product is an explicitly ORDERED recursion
over the full finite mode list; no `Finset.prod` or assumption that arbitrary
continuous linear maps commute is used.

This establishes action on each canonical occupation ket, NOT extraction from
an arbitrary vector, basis completeness or theta_irreducible.
-/

namespace FCP.BFSSFermionF3B4
noncomputable section

open FCP.BFSSFermionF1 FCP.BFSSFermionF2
open FCP.BFSSFermionF3B1 FCP.BFSSFermionF3B2
open FCP.BFSSFermionF3B3

private abbrev BFSSFermion := OAI.BFSSQuantum.Fermion 2
private abbrev BFSSOp := BFSSFermion →L[ℂ] BFSSFermion

/-- The occupied-mode selector or its complement, according to label A. -/
noncomputable def step (A : Finset (Fin 24)) (i : Fin 24) : BFSSOp :=
  if i ∈ A then occupiedMode i else vacantMode i

/-- Complex one-or-zero eigenvalue of the selector on occupation ket B. -/
noncomputable def weight (A B : Finset (Fin 24)) (i : Fin 24) : ℂ :=
  if (i ∈ A ↔ i ∈ B) then 1 else 0

/-- Ordered product: endomorphism multiplication is composition, so the
composition order is fixed by the explicitly provided finite list. -/
noncomputable def selectorSeq (A : Finset (Fin 24)) :
    List (Fin 24) → BFSSOp
  | [] => 1
  | i :: is => step A i * selectorSeq A is

/-- Product of the corresponding complex basis eigenvalues. -/
noncomputable def weightSeq (A B : Finset (Fin 24)) :
    List (Fin 24) → ℂ
  | [] => 1
  | i :: is => weight A B i * weightSeq A B is

/-- The concrete finite selector includes every one of the 24 modes. -/
noncomputable def occupationSelector (A : Finset (Fin 24)) : BFSSOp :=
  selectorSeq A (Finset.univ : Finset (Fin 24)).toList

private theorem step_occupationKet (A B : Finset (Fin 24)) (i : Fin 24) :
    step A i (occupationKet B) = weight A B i • occupationKet B := by
  by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;>
    simp [step, weight, hA, hB,
      occupiedMode_occupationKet, vacantMode_occupationKet]

/-- Every ordered operator product has the same action on a canonical
occupation vector as the product of its genuine zero-or-one eigenvalues. -/
theorem selectorSeq_occupationKet (A B : Finset (Fin 24))
    (is : List (Fin 24)) :
    selectorSeq A is (occupationKet B) =
      weightSeq A B is • occupationKet B := by
  induction is with
  | nil =>
      simp [selectorSeq, weightSeq]
  | cons i is ih =>
      change step A i (selectorSeq A is (occupationKet B)) =
        (weight A B i * weightSeq A B is) • occupationKet B
      rw [ih, map_smul, step_occupationKet, smul_smul]
      exact congrArg (fun c : ℂ => c • occupationKet B)
        (mul_comm (weightSeq A B is) (weight A B i))

private theorem weightSeq_one (A B : Finset (Fin 24)) :
    ∀ is : List (Fin 24),
      (∀ i ∈ is, (i ∈ A ↔ i ∈ B)) → weightSeq A B is = 1 := by
  intro is
  induction is with
  | nil =>
      intro _
      rfl
  | cons i is ih =>
      intro hall
      have hi : (i ∈ A ↔ i ∈ B) := hall i (by simp)
      have htail : ∀ j ∈ is, (j ∈ A ↔ j ∈ B) := by
        intro j hj
        exact hall j (by simp [hj])
      change weight A B i * weightSeq A B is = 1
      rw [ih htail]
      simp [weight, hi]

private theorem weightSeq_zero_of_mismatch (A B : Finset (Fin 24)) :
    ∀ (is : List (Fin 24)) (i : Fin 24),
      i ∈ is → ¬ (i ∈ A ↔ i ∈ B) → weightSeq A B is = 0 := by
  intro is
  induction is with
  | nil =>
      intro i hi _
      simp at hi
  | cons j is ih =>
      intro i hi hm
      simp only [List.mem_cons] at hi
      rcases hi with hEq | hTail
      · subst i
        change weight A B j * weightSeq A B is = 0
        simp [weight, hm]
      · change weight A B j * weightSeq A B is = 0
        rw [ih i hTail hm, mul_zero]

/-- The concrete selector for occupation A fixes exactly that occupation
ket and kills every DIFFERENT occupation ket. This is still a basis-vector
statement, not yet extraction from arbitrary BFSS vectors. -/
theorem occupationSelector_occupationKet
    (A B : Finset (Fin 24)) :
    occupationSelector A (occupationKet B) =
      if A = B then occupationKet B else 0 := by
  change selectorSeq A (Finset.univ : Finset (Fin 24)).toList
      (occupationKet B) = _
  rw [selectorSeq_occupationKet]
  by_cases hAB : A = B
  · subst B
    have hall :
        ∀ i ∈ (Finset.univ : Finset (Fin 24)).toList, (i ∈ A ↔ i ∈ A) := by
      simp
    have hw :
        weightSeq A A (Finset.univ : Finset (Fin 24)).toList = 1 :=
      weightSeq_one A A _ hall
    simp [hw]
  · have hdiff : ∃ i : Fin 24, ¬ (i ∈ A ↔ i ∈ B) := by
      by_contra hn
      apply hAB
      ext i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hm⟩ := hdiff
    have himem : i ∈ (Finset.univ : Finset (Fin 24)).toList := by simp
    have hw :
        weightSeq A B (Finset.univ : Finset (Fin 24)).toList = 0 :=
      weightSeq_zero_of_mismatch A B _ i himem hm
    simp only [hw, zero_smul, _root_.ite_eq_right hAB]

#print axioms selectorSeq_occupationKet
#print axioms occupationSelector_occupationKet

end
end FCP.BFSSFermionF3B4
