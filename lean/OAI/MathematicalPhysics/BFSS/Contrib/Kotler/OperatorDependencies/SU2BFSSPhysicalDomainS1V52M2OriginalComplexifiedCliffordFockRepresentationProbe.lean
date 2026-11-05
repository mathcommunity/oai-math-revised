import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52M1IndependentNonzeroMajoranaIntertwinerEquivProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5C1OriginalFockCliffordAlgebraUniversalLiftProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange

/-!
S1V52-M2 — The genuine ORIGINAL real Clifford(48) Fock algebra
representation extends to the COMPLEXIFIED Clifford algebra.

This is a strictly source-based next step toward constructing
an independent manuscript-module intertwiner. Pinned Mathlib's
CliffordAlgebra.toBaseChange and Algebra.TensorProduct.lift
are algebra homomorphisms; no vector-space-only substitution
or assumed comparison to an arbitrary independent module.

Proving the homomorphism and exact pure generator action does
NOT prove that it is surjective/faithful onto the entire complex
Fock endomorphism algebra. This will require source irreducibility,
complex Schur scalar commutant and Jacobson density / Burnside, or
explicit source CAR matrix units. It also does NOT construct the
independent manuscript's Hilbert unitary, spin representation or
the unbounded physical operator domains.
-/

set_option autoImplicit false
set_option maxHeartbeats 360000

namespace FCP.BFSSS1V52M2
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V52L9E4
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5B
open scoped TensorProduct

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- Real source Clifford action complexified as an ACTUAL complex
algebra homomorphism on the genuine original 24-mode Fock space. -/
noncomputable def originalComplexCliffordFockAlgHom :
    CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] FockOp :=
  (Algebra.TensorProduct.lift
    (Algebra.ofId ℂ FockOp)
    originalFockCliffordAlgHom
    (fun _a _x => Algebra.commutes _ _)).comp
      (CliffordAlgebra.toBaseChange ℂ Q)

/-- The complexified representation agrees on every source 48-real
generator with the accepted original gamma operator, preserving the
exact real-to-complex normalization and Majorana label convention. -/
theorem originalComplexCliffordFockAlgHom_generator
    (v : Source48Vector) :
    originalComplexCliffordFockAlgHom
      (CliffordAlgebra.ι (Q.baseChange ℂ) (1 ⊗ₜ[ℝ] v)) =
      originalFockGammaRealLinear v := by
  have hpure :
      (Algebra.TensorProduct.lift
        (Algebra.ofId ℂ FockOp)
        originalFockCliffordAlgHom
        (fun _a _x => Algebra.commutes _ _))
          (1 ⊗ₜ[ℝ] (CliffordAlgebra.ι Q) v) =
        originalFockGammaRealLinear v := by
    change (Algebra.ofId ℂ FockOp) (1 : ℂ) *
        originalFockCliffordAlgHom (CliffordAlgebra.ι Q v) =
          originalFockGammaRealLinear v
    simpa only [map_one, one_mul] using
      originalFockCliffordAlgHom_generator v
  simpa only [originalComplexCliffordFockAlgHom, AlgHom.coe_comp,
    Function.comp_apply, CliffordAlgebra.toBaseChange_ι] using hpure

#print axioms originalComplexCliffordFockAlgHom
#print axioms originalComplexCliffordFockAlgHom_generator

end
end FCP.BFSSS1V52M2
