import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5E2OriginalAllRealVectorFockGammaSelfAdjointProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5C1OriginalFockCliffordAlgebraUniversalLiftProbe

/-!
S1V52L9E5E3 — RESEARCH CANDIDATE, NOT YET QUALIFIED.

Clifford star on an ODD source generator flips its sign:
star (ι Q u) = -(ι Q u).
The real gamma image on original Fock is self-adjoint, not
skew-adjoint. Thus the real algebra representation is NOT
a star hom globally.

For products of TWO original real generators, both Clifford
star signs cancel. Independently prove that the actual original
Fock Clifford representation intertwines source Clifford star
with Fock adjoint on each genuine source bivector product.

This is only a degree-two/even-generator proof. Extension to all
even Clifford elements, actual native Spin(48) elements, original
gauge unitary implementers, and BFSS spectrum are SEPARATE
unproved obligations. Require independently accepted L9E5E2
and exact source-pinned gate before claiming this root.
-/

set_option autoImplicit false
set_option maxHeartbeats 320000

namespace FCP.BFSSS1V52L9E5E3
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L9E4
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5E2

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- The actual original Fock Clifford-algebra representation
is star-compatible on genuine products of TWO original
48-real source Clifford generators; no global star property
is assumed or inferred. -/
theorem originalFockCliffordAlgHom_star_sourceBivector
    (u v : Source48Vector) :
    originalFockCliffordAlgHom
      (star (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v)) =
    star (originalFockCliffordAlgHom
      (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v)) := by
  have hcl :
      star (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) =
        CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q u := by
    simp only [star_mul, CliffordAlgebra.star_ι, neg_mul_neg]
  calc
    originalFockCliffordAlgHom
        (star (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v)) =
      originalFockCliffordAlgHom
        (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q u) := by
          rw [hcl]
    _ = originalFockGammaRealLinear v *
          originalFockGammaRealLinear u := by
            rw [map_mul, originalFockCliffordAlgHom_generator,
              originalFockCliffordAlgHom_generator]
    _ = star (originalFockGammaRealLinear u *
          originalFockGammaRealLinear v) := by
            -- Gate E2 negative knowledge: on original Fock operators
            -- generic star_mul can pick the wrong star instance.
            -- Use the exact Hilbert-adjoint anti-multiplicativity.
            have hadj :
                ContinuousLinearMap.adjoint
                    (originalFockGammaRealLinear u *
                      originalFockGammaRealLinear v) =
                  originalFockGammaRealLinear v *
                    originalFockGammaRealLinear u := by
              change ContinuousLinearMap.adjoint
                  (originalFockGammaRealLinear u ∘L
                    originalFockGammaRealLinear v) =
                originalFockGammaRealLinear v ∘L
                  originalFockGammaRealLinear u
              rw [ContinuousLinearMap.adjoint_comp,
                (originalFockGammaRealLinear_selfAdjoint v).adjoint_eq,
                (originalFockGammaRealLinear_selfAdjoint u).adjoint_eq]
            exact (ContinuousLinearMap.star_eq_adjoint
              (originalFockGammaRealLinear u *
                originalFockGammaRealLinear v)).trans hadj |>.symm
    _ = star (originalFockCliffordAlgHom
          (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v)) := by
            rw [map_mul, originalFockCliffordAlgHom_generator,
              originalFockCliffordAlgHom_generator]

#print axioms originalFockCliffordAlgHom_star_sourceBivector

end
end FCP.BFSSS1V52L9E5E3
