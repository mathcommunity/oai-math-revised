import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F5OriginalFiniteRealBivectorWordLinearCombinationFockAdjointProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52B2Original48CliffordQuaternionPolynomialMulProbe

/-!
S1V52L9E5F6 — STAGED / UNQUALIFIED; one actual-source root.

Specializes the verified *conditional* even-source star/adjoint
transport to the ACTUAL original 48-Clifford block quaternion
  sourceCliffordQuaternion α p
    = p.a • 1 + p.b • Zα + p.c • Yα + p.d • Xα.
Each Z,Y,X is exactly a pair of original Source48Vector
Clifford generators, not a surrogate quaternion or Clifford model.

Use accepted E3 (each pair), F2 (unit), F3 (conditional
sum) and F4 (real smul), with small named intermediate
proofs instead of a large simp/unfold to prevent an F5-G1
heartbeats regression. F5 has separately already proved the
general finite even-real span; the present root is an exact
connection to the actual original named quaternion expression.

This is NOT yet a proof of unitary Fock image, let alone
full native Spin(48), physical gauge implementer identity,
or BFSS spectrum.
-/

set_option autoImplicit false
set_option maxHeartbeats 360000

namespace FCP.BFSSS1V52L9E5F6
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52A
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B2
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5E3
open FCP.BFSSS1V52L9E5F2
open FCP.BFSSS1V52L9E5F3
open FCP.BFSSS1V52L9E5F4

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Actual original 48-real Clifford block quaternion star
is mapped to the ACTUAL Fermion-2 Hilbert operator adjoint.
This claim is scoped to the source 4-term quaternion and
does not assert a global star hom on odd Clifford vectors. -/
theorem originalFockCliffordAlgHom_star_sourceQuaternion
    (α : RealSpinBlock) (p : SourceQuaternionCoords) :
    originalFockCliffordAlgHom (star (sourceCliffordQuaternion α p)) =
      star (originalFockCliffordAlgHom (sourceCliffordQuaternion α p)) := by
  have hOne :
      originalFockCliffordAlgHom (star (1 : C)) =
        star (originalFockCliffordAlgHom (1 : C)) :=
    originalFockCliffordAlgHom_star_one
  have hZ :
      originalFockCliffordAlgHom (star (sourceZBivector α)) =
        star (originalFockCliffordAlgHom (sourceZBivector α)) := by
    change originalFockCliffordAlgHom
        (star (CliffordAlgebra.ι Q (sourceBlockColorAxis α 0) *
          CliffordAlgebra.ι Q (sourceBlockColorAxis α 1))) =
      star (originalFockCliffordAlgHom
        (CliffordAlgebra.ι Q (sourceBlockColorAxis α 0) *
          CliffordAlgebra.ι Q (sourceBlockColorAxis α 1)))
    exact originalFockCliffordAlgHom_star_sourceBivector _ _
  have hY :
      originalFockCliffordAlgHom (star (sourceYBivector α)) =
        star (originalFockCliffordAlgHom (sourceYBivector α)) := by
    change originalFockCliffordAlgHom
        (star (CliffordAlgebra.ι Q (sourceBlockColorAxis α 2) *
          CliffordAlgebra.ι Q (sourceBlockColorAxis α 0))) =
      star (originalFockCliffordAlgHom
        (CliffordAlgebra.ι Q (sourceBlockColorAxis α 2) *
          CliffordAlgebra.ι Q (sourceBlockColorAxis α 0)))
    exact originalFockCliffordAlgHom_star_sourceBivector _ _
  have hX :
      originalFockCliffordAlgHom (star (sourceXBivector α)) =
        star (originalFockCliffordAlgHom (sourceXBivector α)) := by
    change originalFockCliffordAlgHom
        (star (CliffordAlgebra.ι Q (sourceBlockColorAxis α 1) *
          CliffordAlgebra.ι Q (sourceBlockColorAxis α 2))) =
      star (originalFockCliffordAlgHom
        (CliffordAlgebra.ι Q (sourceBlockColorAxis α 1) *
          CliffordAlgebra.ι Q (sourceBlockColorAxis α 2)))
    exact originalFockCliffordAlgHom_star_sourceBivector _ _
  have ha := originalFockCliffordAlgHom_star_real_smul_of
    p.a (1 : C) hOne
  have hb := originalFockCliffordAlgHom_star_real_smul_of
    p.b (sourceZBivector α) hZ
  have hc := originalFockCliffordAlgHom_star_real_smul_of
    p.c (sourceYBivector α) hY
  have hd := originalFockCliffordAlgHom_star_real_smul_of
    p.d (sourceXBivector α) hX
  have hab := originalFockCliffordAlgHom_star_add_of
    (p.a • (1 : C)) (p.b • sourceZBivector α) ha hb
  have habc := originalFockCliffordAlgHom_star_add_of
    (p.a • (1 : C) + p.b • sourceZBivector α)
    (p.c • sourceYBivector α) hab hc
  have habcd := originalFockCliffordAlgHom_star_add_of
    (p.a • (1 : C) + p.b • sourceZBivector α +
      p.c • sourceYBivector α)
    (p.d • sourceXBivector α) habc hd
  change originalFockCliffordAlgHom
      (star (p.a • (1 : C) + p.b • sourceZBivector α +
        p.c • sourceYBivector α + p.d • sourceXBivector α)) =
    star (originalFockCliffordAlgHom
      (p.a • (1 : C) + p.b • sourceZBivector α +
        p.c • sourceYBivector α + p.d • sourceXBivector α))
  exact habcd

#print axioms originalFockCliffordAlgHom_star_sourceQuaternion

end
end FCP.BFSSS1V52L9E5F6
