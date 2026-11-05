import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSSource48RealLinearGammaProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSSource48QuadraticUnitAxesProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52L9E5A2FiniteComplexWeightedFockCliffordSquareProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52L9E5B0OriginalFockRealComplexOperatorScalarBridgeProbe
import Mathlib.Basic.Complex.BigOperators

/-!
# All-vector original Source48 Fock Clifford quadratic square

The original 48-real source, positive source48Quadratic, and Fermion 2
complex-linear endomorphisms are unchanged.  The proof specializes the
finite COMPLEX-weighted CAR-square lemma to the now-qualified real-linear
sqrt(2)-normalized Source48 Fock gammas and uses a separate, explicit
real/complex operator scalar bridge. It does not infer arbitrary-vector
Clifford algebra compatibility merely from the basis CAR.

Adapted from original FCP L9E5B after FCP L9E5A Gate 1–2 established
that directly rewriting real-scalar Fock multiplication was unsafe.
No universal Clifford AlgHom, group-unitary gauge action, or BFSS spectral
statement is asserted by this one square theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSSource48AllVectorFockCliffordSquare
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSSource48NormalizedFockGamma
open FCP.BFSSSource48RealLinearGamma
open FCP.BFSSSource48QuadraticUnitAxes
open FCP.BFSSS1V52L9E5A2
open FCP.BFSSS1V52L9E5B0

private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- The genuine original Source48 real-linear Fock operator has
the original positive Clifford square for every real source vector. -/
theorem sourceGammaRealLinear_sq (v : Source48Vector) :
    sourceGammaRealLinear v * sourceGammaRealLinear v =
      (source48Quadratic v) • (1 : FockOp) := by
  classical
  let γ (p : Source48Label) : FockOp := sourceNormalizedGamma p
  let cc (p : Source48Label) : ℂ := (v p : ℂ)
  have hdiag (p : Source48Label) : γ p * γ p = (1 : FockOp) :=
    sourceNormalizedGamma_sq_one p
  have hanti (p q : Source48Label) (hpq : p ≠ q) :
      γ p * γ q + γ q * γ p = 0 := by
    calc
      γ p * γ q + γ q * γ p = (0 : ℂ) • (1 : FockOp) := by
        simpa only [γ, ite_eq_right hpq] using
          (sourceNormalizedGamma_pairwise_CAR p q)
      _ = 0 := zero_smul ℂ (1 : FockOp)
  have hcomplex :
      (∑ p : Source48Label, cc p • γ p) *
        (∑ p : Source48Label, cc p • γ p) =
      (∑ p : Source48Label, cc p * cc p) • (1 : FockOp) :=
    finiteComplexWeightedFockClifford_square
      (Finset.univ : Finset Source48Label) cc γ hdiag hanti
  have hrealToComplex :
      (∑ p : Source48Label, (v p) • γ p) =
        ∑ p : Source48Label, cc p • γ p := by
    apply Finset.sum_congr rfl
    intro p hp
    exact originalFockOperator_real_smul_eq_complex_smul (v p) (γ p)
  have hcoeff :
      (∑ p : Source48Label, cc p * cc p) =
        ((∑ p : Source48Label, v p * v p : ℝ) : ℂ) := by
    calc
      (∑ p : Source48Label, cc p * cc p) =
          ∑ p : Source48Label, ((v p * v p : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro p hp
        change (v p : ℂ) * (v p : ℂ) =
          ((v p * v p : ℝ) : ℂ)
        exact (Complex.ofReal_mul (v p) (v p)).symm
      _ = ((∑ p : Source48Label, v p * v p : ℝ) : ℂ) :=
        (Complex.ofReal_sum (Finset.univ : Finset Source48Label)
          (fun p => v p * v p)).symm
  calc
    sourceGammaRealLinear v * sourceGammaRealLinear v =
        (∑ p : Source48Label, (v p) • γ p) *
          (∑ p : Source48Label, (v p) • γ p) := by rfl
    _ = (∑ p : Source48Label, cc p • γ p) *
          (∑ p : Source48Label, cc p • γ p) := by rw [hrealToComplex]
    _ = (∑ p : Source48Label, cc p * cc p) • (1 : FockOp) := hcomplex
    _ = (∑ p : Source48Label, v p * v p) • (1 : FockOp) := by
      rw [hcoeff]
      exact
        (originalFockOperator_real_smul_eq_complex_smul
          (∑ p : Source48Label, v p * v p) (1 : FockOp)).symm
    _ = (source48Quadratic v) • (1 : FockOp) := by
      rw [FCP.BFSSSource48QuadraticUnitAxes.source48Quadratic_eq_dot]
      rfl

#print axioms sourceGammaRealLinear_sq

end
end FCP.BFSSSource48AllVectorFockCliffordSquare
