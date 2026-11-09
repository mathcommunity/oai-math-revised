import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E3OriginalFockNormalizedMajoranaPairwiseCliffordCARProbe

/-!
S1V52L9E4 — UNQUALIFIED exact ORIGINAL real-linear source
Clifford-generator candidate on the ORIGINAL Fermion 2 Fock module.

The original source 48-real coordinate vector is (Fin24×Fin2) → ℝ.
The sourceBlockColorEquiv is the already accepted 16×3↔48 source
Fock-Majorana label identification. Normalize the ORIGINAL pairedTheta
by positive real sqrt(2) as strictly accepted L9E2/L9E3, then extend
linearly by a finite sum over the *actual original source labels*.

One qualified-root target: the real-linear generator map sends
every actual source block/color axis to its exact normalized original
Fock Majorana operator. Defining a linear map is not yet construction
of a Clifford algebra representation: the all-vector quadratic-square
identity remains a separately required theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52L9E4
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L9E2
open FCP.BFSSS1V52L9E3

/-- Real-linear extension on ALL original BFSS 48-real source
vectors of the strictly verified original positive-sqrt2
normalized Fock Majorana generators. -/
noncomputable def originalFockGammaRealLinear :
    Source48Vector →ₗ[ℝ] (Fermion 2 →L[ℂ] Fermion 2) where
  toFun v :=
    ∑ p : SourceLabel,
      (v p) • originalNormalizedFockMajorana
        (sourceBlockColorEquiv.symm p).1
        (sourceBlockColorEquiv.symm p).2
  map_add' := by
    intro v w
    -- Separate the pointwise REAL sum from the operator-valued
    -- finite sum, with explicit scalar distributivity at each label.
    change (∑ p : SourceLabel, (v p + w p) •
        originalNormalizedFockMajorana
          (sourceBlockColorEquiv.symm p).1
          (sourceBlockColorEquiv.symm p).2) =
      (∑ p : SourceLabel, (v p) •
        originalNormalizedFockMajorana
          (sourceBlockColorEquiv.symm p).1
          (sourceBlockColorEquiv.symm p).2) +
      (∑ p : SourceLabel, (w p) •
        originalNormalizedFockMajorana
          (sourceBlockColorEquiv.symm p).1
          (sourceBlockColorEquiv.symm p).2)
    calc
      (∑ p : SourceLabel, (v p + w p) •
          originalNormalizedFockMajorana
            (sourceBlockColorEquiv.symm p).1
            (sourceBlockColorEquiv.symm p).2) =
        ∑ p : SourceLabel,
          ((v p) • originalNormalizedFockMajorana
            (sourceBlockColorEquiv.symm p).1
            (sourceBlockColorEquiv.symm p).2 +
          (w p) • originalNormalizedFockMajorana
            (sourceBlockColorEquiv.symm p).1
            (sourceBlockColorEquiv.symm p).2) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact add_smul (v p) (w p)
            (originalNormalizedFockMajorana
              (sourceBlockColorEquiv.symm p).1
              (sourceBlockColorEquiv.symm p).2)
      _ = _ := Finset.sum_add_distrib
  map_smul' := by
    intro c v
    -- Normalize the ACTUAL map_smul' target rather than
    -- invoking change across Pi.smul_apply, RingHom.id ℝ and
    -- Finset.smul_sum, none of which is definitional reduction.
    simp only [Pi.smul_apply, RingHom.id_apply,
      Finset.smul_sum, smul_smul, smul_eq_mul]

/-- This genuine real-linear Fock generator map sends each
ORIGINAL source 48-real Majorana coordinate axis to the
corresponding exact original normalized pairedTheta operator. -/
theorem originalFockGammaRealLinear_sourceAxis
    (α : RealSpinBlock) (A : Fin 3) :
    originalFockGammaRealLinear (sourceBlockColorAxis α A) =
      originalNormalizedFockMajorana α A := by
  classical
  change (∑ p : SourceLabel,
      (sourceBlockColorAxis α A p) •
        originalNormalizedFockMajorana
          (sourceBlockColorEquiv.symm p).1
          (sourceBlockColorEquiv.symm p).2) =
      originalNormalizedFockMajorana α A
  rw [Finset.sum_eq_single (sourceBlockColorLabel α A)]
  · have hlabel :
        sourceBlockColorEquiv.symm (sourceBlockColorLabel α A) =
          (α, A) := by
      exact sourceBlockColorEquiv.symm_apply_apply (α, A)
    rw [sourceBlockColorAxis_self]
    simp only [one_smul]
    rw [hlabel]
  · intro p hp hneq
    have hzero : sourceBlockColorAxis α A p = 0 := by
      -- L9E4 Gate #2: sourceBlockColorAxis is a Pi.single
      -- source coordinate, not syntactically its if expression.
      simp only [sourceBlockColorAxis, Pi.single_apply]
      exact _root_.ite_eq_right hneq
    -- The original ℝ-scaled Fock continuous-linear operator has
    -- a concrete zero-scalar identity, not an inferred metavariable.
    -- Gate #3's simp [hzero] did not close this exact goal.
    rw [hzero]
    exact zero_smul ℝ
      (originalNormalizedFockMajorana
        (sourceBlockColorEquiv.symm p).1
        (sourceBlockColorEquiv.symm p).2 :
          Fermion 2 →L[ℂ] Fermion 2)
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

#print axioms originalFockGammaRealLinear_sourceAxis

end
end FCP.BFSSS1V52L9E4
