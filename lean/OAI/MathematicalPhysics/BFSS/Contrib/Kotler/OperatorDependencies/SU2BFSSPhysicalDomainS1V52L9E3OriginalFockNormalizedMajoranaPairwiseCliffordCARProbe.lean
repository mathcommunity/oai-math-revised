import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E2OriginalFockMajoranaSourceCliffordAxisNormalizationProbe

/-!
S1V52L9E3 — STAGED, UNQUALIFIED, dependent on kernel acceptance
of L9E2. Original Fermion 2 complex-linear Majoranas normalized
by sqrt(2) satisfy the exact unit-Clifford pairwise anticommutator.

Original source pairedTheta CAR is delta ONE. On unit source
axes the positive-sign Clifford Q satisfies Q(e)=1, hence
gamma(e)^2=1 and gamma(e)gamma(f)+gamma(f)gamma(e)=
2 delta(e,f) I. Original real/imag Fock labeling and
source spinPairEquiv.symm pairing must remain EXACT.

This stage is NOT a constructed full CliffordAlgebra AlgHom,
Fock-unitary Spin representation, topological lift or spectral
statement. Strict CI must verify all axioms before qualification.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52L9E3
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V5
open FCP.BFSSS1V52L9E2
open FCP.BFSSSU2GaugeG1A

/-- The two sqrt(2)-normalized ORIGINAL Fock Majoranas have
the exact positive-unit Clifford anticommutator, including the
correct delta factor two. -/
theorem originalNormalizedFockMajorana_pairwise_CAR
    (α β : RealSpinBlock) (A B : Fin 3) :
    originalNormalizedFockMajorana α A *
        originalNormalizedFockMajorana β B +
      originalNormalizedFockMajorana β B *
        originalNormalizedFockMajorana α A =
      (if α = β ∧ A = B then (2 : ℂ) else 0) •
        (1 : Fermion 2 →L[ℂ] Fermion 2) := by
  let x : Fermion 2 →L[ℂ] Fermion 2 :=
    pairedTheta (spinPairEquiv.symm α) A
  let y : Fermion 2 →L[ℂ] Fermion 2 :=
    pairedTheta (spinPairEquiv.symm β) B
  have hlabel :
      (spinPairEquiv.symm α = spinPairEquiv.symm β ∧ A = B) ↔
        (α = β ∧ A = B) := by
    constructor
    · rintro ⟨hs, hAB⟩
      exact ⟨spinPairEquiv.symm.injective hs, hAB⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  have hcar : x * y + y * x =
      (if α = β ∧ A = B then (1 : ℂ) else 0) •
        (1 : Fermion 2 →L[ℂ] Fermion 2) := by
    have hc := pairedTheta_CAR
      (spinPairEquiv.symm α) (spinPairEquiv.symm β) A B
    change x * y + y * x =
      (if spinPairEquiv.symm α = spinPairEquiv.symm β ∧ A = B
         then (1 : ℂ) else 0) •
        (1 : Fermion 2 →L[ℂ] Fermion 2) at hc
    by_cases hab : α = β ∧ A = B
    · have hh := hlabel.mpr hab
      simpa only [_root_.ite_eq_left hh, _root_.ite_eq_left hab] using hc
    · have hn :
          ¬ (spinPairEquiv.symm α = spinPairEquiv.symm β ∧ A = B) := by
        intro h
        exact hab (hlabel.mp h)
      simpa only [_root_.ite_eq_right hn, _root_.ite_eq_right hab] using hc
  have hsqrt : ((↑(Real.sqrt 2) : ℂ) *
      (↑(Real.sqrt 2) : ℂ)) = (2 : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  -- First aggregate the two original Fock operator products
  -- with the *explicitly typed same complex scalar*. Reverse
  -- rewriting smul_add directly on elaborated √2 terms failed in
  -- Gate #1 despite the visible identical coefficients.
  let c : ℂ := ↑(Real.sqrt 2)
  have hc2 : c * c = (2 : ℂ) := hsqrt
  change (c • x) * (c • y) + (c • y) * (c • x) =
      (if α = β ∧ A = B then (2 : ℂ) else 0) •
        (1 : Fermion 2 →L[ℂ] Fermion 2)
  calc
    (c • x) * (c • y) + (c • y) * (c • x) =
        (c * c) • (x * y + y * x) := by
      calc
        (c • x) * (c • y) + (c • y) * (c • x) =
            (c * c) • (x * y) + (c * c) • (y * x) := by
              rw [smul_mul_smul, smul_mul_smul]
        _ = (c * c) • (x * y + y * x) :=
          (smul_add (c * c) (x * y) (y * x)).symm
    _ = (2 : ℂ) • (x * y + y * x) := by rw [hc2]
    _ = (2 : ℂ) •
          ((if α = β ∧ A = B then (1 : ℂ) else 0) •
            (1 : Fermion 2 →L[ℂ] Fermion 2)) := by rw [hcar]
    _ = (if α = β ∧ A = B then (2 : ℂ) else 0) •
          (1 : Fermion 2 →L[ℂ] Fermion 2) := by
      by_cases hab : α = β ∧ A = B <;>
        simp [hab, smul_smul]

#print axioms originalNormalizedFockMajorana_pairwise_CAR

end
end FCP.BFSSS1V52L9E3
