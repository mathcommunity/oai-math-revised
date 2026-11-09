import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F3OriginalCliffordFockStarAdditiveClosureProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52L9E5B0OriginalFockRealComplexOperatorScalarBridgeProbe

/-!
S1V52L9E5F4 — STAGED ONLY; NOT KERNEL QUALIFIED.
Real coefficient compatibility of genuine ORIGINAL source
Clifford star with actual Fermion 2 Hilbert adjoint, conditional
on compatibility for the underlying source element.

Pivotal source convention: Clifford star anti-negates ODD
generators. No global Clifford star algebra homomorphism follows.
Pinned `CliffordAlgebra.star_smul` acts on real source
coefficients; the true Fock adjoint is the conjugate-linear
`ContinuousLinearMap.adjoint`, with real complex coefficient
fixed by complex conjugation. Reuse L9E5B0 for the exact
original real-to-complex Fock continuous-linear-operator
scalar-action instance.

This intended theorem, combined with accepted F2 and
pending F3, will allow finite REAL linear combinations of
original ordered Clifford bivector words; not yet native Spin
or physical BFSS gauge unitarity.
-/

set_option autoImplicit false
set_option maxHeartbeats 340000

namespace FCP.BFSSS1V52L9E5F4
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5F3
open FCP.BFSSS1V52L9E5B0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- Compatibility of source Clifford star with actual Fock
adjoint is stable under REAL scalar multiplication,
conditional on compatibility for the source element. -/
theorem originalFockCliffordAlgHom_star_real_smul_of
    (a : ℝ) (x : C)
    (hx : originalFockCliffordAlgHom (star x) =
      star (originalFockCliffordAlgHom x)) :
    originalFockCliffordAlgHom (star (a • x)) =
      star (originalFockCliffordAlgHom (a • x)) := by
  have hadj (T : FockOp) :
      star (a • T) = a • star T := by
    rw [originalFockOperator_real_smul_eq_complex_smul a T,
      originalFockOperator_real_smul_eq_complex_smul a (star T)]
    change ContinuousLinearMap.adjoint ((a : ℂ) • T) =
      (a : ℂ) • ContinuousLinearMap.adjoint T
    simp only [map_smulₛₗ, Complex.conj_ofReal]
  calc
    originalFockCliffordAlgHom (star (a • x)) =
        originalFockCliffordAlgHom (a • star x) := by
          rw [CliffordAlgebra.star_smul]
    _ = a • originalFockCliffordAlgHom (star x) := by
          exact map_smul originalFockCliffordAlgHom a (star x)
    _ = a • star (originalFockCliffordAlgHom x) := by
          rw [hx]
    _ = star (a • originalFockCliffordAlgHom x) := by
          exact (hadj _).symm
    _ = star (originalFockCliffordAlgHom (a • x)) := by
          rw [map_smul]

#print axioms originalFockCliffordAlgHom_star_real_smul_of

end
end FCP.BFSSS1V52L9E5F4
