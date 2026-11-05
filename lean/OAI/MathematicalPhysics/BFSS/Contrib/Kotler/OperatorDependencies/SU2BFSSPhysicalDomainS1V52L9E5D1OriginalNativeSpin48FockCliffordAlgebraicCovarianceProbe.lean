import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5C1OriginalFockCliffordAlgebraUniversalLiftProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E1OriginalNativeSixteenSpin48UniversalCliffordConjugationProbe

/-!
S1V52L9E5D1 — STAGED ONLY, NOT YET KERNEL-QUALIFIED.

Transport the ACCEPTED exact original Clifford Spin(48) conjugation
identity (L9E1) along the newly kernel-accepted REAL Clifford algebra
representation into genuine original Fermion 2 complex-linear operators
(L9E5C1).

The RIGHT factor is deliberately
  originalFockCliffordAlgHom (star (spin : CliffordAlgebra Q))
and NOT `star (originalFockCliffordAlgHom spin)`.

An algebra homomorphism need not preserve star automatically; equating
those two operators requires an independent proof. Therefore the
result below is algebraic original-Fock covariance, NOT a proved
unitary/adjoint gauge implementation, irreducibility, or BFSS gap.

The full original 48-source real gauge matrix, exact original SU2→
Spin48 hom, and actual Fock generators are retained unchanged.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52L9E5D1
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L8E
open FCP.BFSSS1V52L9E1
open FCP.BFSSS1V52L9E4
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSSU2PhysicalDomainS1J

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- Every abstract Clifford conjugation of an ORIGINAL source
generator transports multiplicatively under the qualified original
Fock Clifford algebra representation. This makes NO assumption that
the Fock representation is star-preserving. -/
theorem originalFockCliffordAlgHom_conj_generator
    (s : C) (v : Source48Vector) :
    originalFockCliffordAlgHom
        (s * CliffordAlgebra.ι Q v * star s) =
      originalFockCliffordAlgHom s *
        originalFockGammaRealLinear v *
          originalFockCliffordAlgHom (star s) := by
  calc
    originalFockCliffordAlgHom
        (s * CliffordAlgebra.ι Q v * star s) =
      originalFockCliffordAlgHom s *
        originalFockCliffordAlgHom (CliffordAlgebra.ι Q v) *
          originalFockCliffordAlgHom (star s) := by
            rw [map_mul, map_mul]
    _ = originalFockCliffordAlgHom s *
          originalFockGammaRealLinear v *
            originalFockCliffordAlgHom (star s) := by
              rw [originalFockCliffordAlgHom_generator]

/-- Source-exact algebraic Fock covariance for the actual native
SU(2) → Spin(48) lift. Both factors are images of the GENUINE
original Clifford Spin element, and the right factor is the image
of Clifford star (not yet identified with Fock adjoint).
No physical group-unitary implementation is assumed. -/
theorem originalNativeSpinFock_clifford_generator_covariance
    (g : GaugeGroup 2) (v : Source48Vector) :
    originalFockCliffordAlgHom
        ((originalNativeSixteenSpinHom g : spinGroup Q) : C) *
      originalFockGammaRealLinear v *
        originalFockCliffordAlgHom
          (star ((originalNativeSixteenSpinHom g : spinGroup Q) : C)) =
      originalFockGammaRealLinear
        ((sourceRealMajoranaMatrix g).mulVec v) := by
  have h := congrArg originalFockCliffordAlgHom
    (originalNativeSixteenSpinHom_clifford_generator_conj g v)
  rw [originalFockCliffordAlgHom_conj_generator,
    originalFockCliffordAlgHom_generator] at h
  exact h

#print axioms originalFockCliffordAlgHom_conj_generator
#print axioms originalNativeSpinFock_clifford_generator_covariance

end
end FCP.BFSSS1V52L9E5D1
