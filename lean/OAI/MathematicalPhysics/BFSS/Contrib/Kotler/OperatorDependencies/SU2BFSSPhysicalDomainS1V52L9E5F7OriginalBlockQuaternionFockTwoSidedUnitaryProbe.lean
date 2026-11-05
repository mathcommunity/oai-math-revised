import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F6OriginalBlockQuaternionFockStarAdjointBridgeProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52S1Original48CliffordQuaternionStarUnitarityProbe

/-!
S1V52L9E5F7 — STAGED / NOT KERNEL QUALIFIED.

Actual ORIGINAL positive-norm 48-real Clifford block quaternion,
actual `originalFockCliffordAlgHom` into the ORIGINAL Fermion 2
complex-linear continuous-operator algebra, and actual Hilbert
adjoint star.

For a norm-one source quaternion, source S1 already gives
BOTH genuine source-Clifford star-inverse equalities, and
qualified F6 gives exact star/adjoint compatibility on the
true 4-term source quaternion polynomial. Apply the genuine
real algebra hom's multiplication and identity laws to
transport BOTH unit equations to actual original Fock.

This proves only unitary OPERATOR IMAGES of norm-one original
source block quaternions, not that every Spin(48) element is
a product of such source quaternion polynomials or that the
Fock image equals original physical gauge implementation.
It proves no BFSS spectral property.
-/

set_option autoImplicit false
set_option maxHeartbeats 320000

namespace FCP.BFSSS1V52L9E5F7
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B2
open FCP.BFSSS1V52B3
open FCP.BFSSS1V52S1
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5F6

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- Left actual Fock adjoint inverse for the norm-one genuine
source 48-Clifford quaternion image. Not a surrogate unitary. -/
theorem originalFockBlockQuaternion_adjoint_mul
    (α : RealSpinBlock) (p : SourceQuaternionCoords)
    (hp : sourceQuaternionNormSq p = 1) :
    star (originalFockCliffordAlgHom (sourceCliffordQuaternion α p)) *
      originalFockCliffordAlgHom (sourceCliffordQuaternion α p) =
      (1 : FockOp) := by
  let q : C := sourceCliffordQuaternion α p
  have hcompat :
      originalFockCliffordAlgHom (star q) =
      star (originalFockCliffordAlgHom q) :=
    originalFockCliffordAlgHom_star_sourceQuaternion α p
  have hsrc : star q * q = (1 : C) :=
    sourceCliffordQuaternion_star_mul α p hp
  calc
    star (originalFockCliffordAlgHom (sourceCliffordQuaternion α p)) *
      originalFockCliffordAlgHom (sourceCliffordQuaternion α p) =
        originalFockCliffordAlgHom (star q) *
          originalFockCliffordAlgHom q := by
            rw [hcompat]
    _ = originalFockCliffordAlgHom (star q * q) := by
          rw [map_mul]
    _ = (1 : FockOp) := by
          rw [hsrc, map_one]

/-- Right actual Fock adjoint inverse for the norm-one genuine
source 48-Clifford quaternion image. -/
theorem originalFockBlockQuaternion_mul_adjoint
    (α : RealSpinBlock) (p : SourceQuaternionCoords)
    (hp : sourceQuaternionNormSq p = 1) :
    originalFockCliffordAlgHom (sourceCliffordQuaternion α p) *
      star (originalFockCliffordAlgHom (sourceCliffordQuaternion α p)) =
      (1 : FockOp) := by
  let q : C := sourceCliffordQuaternion α p
  have hcompat :
      originalFockCliffordAlgHom (star q) =
      star (originalFockCliffordAlgHom q) :=
    originalFockCliffordAlgHom_star_sourceQuaternion α p
  have hsrc : q * star q = (1 : C) :=
    sourceCliffordQuaternion_mul_star α p hp
  calc
    originalFockCliffordAlgHom (sourceCliffordQuaternion α p) *
      star (originalFockCliffordAlgHom (sourceCliffordQuaternion α p)) =
        originalFockCliffordAlgHom q *
          originalFockCliffordAlgHom (star q) := by
            rw [hcompat]
    _ = originalFockCliffordAlgHom (q * star q) := by
          rw [map_mul]
    _ = (1 : FockOp) := by
          rw [hsrc, map_one]

#print axioms originalFockBlockQuaternion_adjoint_mul
#print axioms originalFockBlockQuaternion_mul_adjoint

end
end FCP.BFSSS1V52L9E5F7
