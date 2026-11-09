import OAI.MathematicalPhysics.BFSS.Core

/-!
S1V52L9E5A2 — STAGED, UNQUALIFIED complex-weighted finite CAR square
on the ACTUAL original Fermion 2 complex-linear operator algebra.

This is the explicit architecture pivot following L9E5A Gate #1–#2
failures at REAL scalar/operator multiplication. The source 48-vector,
original BFSS Fock, positive sqrt(2) normalized CAR and exact labels
are unchanged, but this ABSTRACT contraction works with coefficients
in ℂ (a mathematically stronger scalar domain). Original real-source
specialization requires a SEPARATE, strictly verified real/complex
operator scaling bridge. Do not count this as an original all-vector
BFSS quadratic identity or a CliffordAlgebra.lift.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52L9E5A2
noncomputable section

open OAI.BFSSQuantum

private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

theorem finiteComplexWeightedFockClifford_square
    {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (γ : ι → FockOp)
    (hdiag : ∀ i, γ i * γ i = (1 : FockOp))
    (hanti : ∀ i j, i ≠ j →
      γ i * γ j + γ j * γ i = 0) :
    (∑ i ∈ s, c i • γ i) *
      (∑ i ∈ s, c i • γ i) =
    (∑ i ∈ s, c i * c i) • (1 : FockOp) := by
  classical
  let X : ι → FockOp := fun i => c i • γ i
  have hdiagX (i : ι) :
      X i * X i = (c i * c i) • (1 : FockOp) := by
    change (c i • γ i) * (c i • γ i) =
      (c i * c i) • (1 : FockOp)
    rw [smul_mul_smul, hdiag i]
  have hcrossX (i j : ι) (hij : i ≠ j) :
      X i * X j + X j * X i = 0 := by
    change (c i • γ i) * (c j • γ j) +
      (c j • γ j) * (c i • γ i) = 0
    calc
      (c i • γ i) * (c j • γ j) +
          (c j • γ j) * (c i • γ i) =
        (c i * c j) • (γ i * γ j) +
          (c i * c j) • (γ j * γ i) := by
            rw [smul_mul_smul, smul_mul_smul,
              mul_comm (c j) (c i)]
      _ = (c i * c j) • (γ i * γ j + γ j * γ i) :=
        (smul_add (c i * c j) (γ i * γ j) (γ j * γ i)).symm
      _ = 0 := by
        rw [hanti i j hij]
        -- Gate #2 exposed a mismatch between a generic
        -- SMulZeroClass instance and the *actual*
        -- ContinuousLinearMap.instSMul on original Fock operators.
        -- The scalar-zero equation is established pointwise in the
        -- genuine Fock module, without manufacturing a new instance.
        apply ContinuousLinearMap.ext
        intro ψ
        simp only [smul_apply,
          zero_apply]
        exact (smul_zero (c i * c j) :
          (c i * c j) • (0 : Fermion 2) = 0)
  have hsum (t : Finset ι) :
      (∑ i ∈ t, X i) * (∑ i ∈ t, X i) =
        (∑ i ∈ t, c i * c i) • (1 : FockOp) := by
    induction t using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty, zero_mul]
        exact (zero_smul ℂ (1 : FockOp)).symm
    | @insert i t hi ih =>
        have hcrossSum :
            X i * (∑ j ∈ t, X j) +
              (∑ j ∈ t, X j) * X i = 0 := by
          rw [Finset.mul_sum, Finset.sum_mul,
            ← Finset.sum_add_distrib]
          apply Finset.sum_eq_zero
          intro j hj
          have hij : i ≠ j := by
            intro heq
            subst j
            exact hi hj
          exact hcrossX i j hij
        simp only [Finset.sum_insert hi]
        calc
          (X i + ∑ j ∈ t, X j) *
              (X i + ∑ j ∈ t, X j) =
            X i * X i +
              (∑ j ∈ t, X j) * (∑ j ∈ t, X j) +
              (X i * (∑ j ∈ t, X j) +
                (∑ j ∈ t, X j) * X i) := by
                  noncomm_ring
          _ = (c i * c i) • (1 : FockOp) +
                (∑ j ∈ t, c j * c j) • (1 : FockOp) := by
                  rw [hcrossSum, add_zero, hdiagX i, ih]
          _ = (c i * c i + ∑ j ∈ t, c j * c j) •
                (1 : FockOp) :=
                  (add_smul (c i * c i)
                    (∑ j ∈ t, c j * c j) (1 : FockOp)).symm
  simpa only [X] using hsum s

#print axioms finiteComplexWeightedFockClifford_square

end
end FCP.BFSSS1V52L9E5A2
