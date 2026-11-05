import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5E3OriginalFockSourceBivectorStarAdjointCompatibilityProbe

/-!
S1V52L9E5F1 — STAGED ONLY, UNQUALIFIED.

The original real Clifford algebra `C` has its pinned source
Clifford star. The actual original Fermion 2 operator algebra
has the HILBERT adjoint star. The accepted real algebra map rho
is not a star hom globally: Clifford star negates odd gamma,
whereas original physical Fock gamma is self-adjoint.

This root proves only a mathematically exact CLOSURE RULE:
if two specified original Clifford elements individually satisfy
rho(star x) = star(rho x), then their PRODUCT also does.
This combines source Clifford star anti-multiplicativity with
the TYPED actual Fock adjoint anti-multiplicativity, avoiding
the generic operator star_mul instance mismatch recorded in E2.

The intended subsequent original-even application is to actual
finite products of E3-qualified two-generator Clifford bivectors;
do NOT infer the premise for arbitrary Clifford elements.
-/

set_option autoImplicit false
set_option maxHeartbeats 320000

namespace FCP.BFSSS1V52L9E5F1
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5E3

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- Star/actual Fock adjoint compatibility is closed under
multiplication, provided it has ALREADY been established for
each factor separately. This is NOT a global star hom. -/
theorem originalFockCliffordAlgHom_star_mul_of
    (x y : C)
    (hx : originalFockCliffordAlgHom (star x) =
      star (originalFockCliffordAlgHom x))
    (hy : originalFockCliffordAlgHom (star y) =
      star (originalFockCliffordAlgHom y)) :
    originalFockCliffordAlgHom (star (x * y)) =
      star (originalFockCliffordAlgHom (x * y)) := by
  have hadj (A B : FockOp) :
      star (A * B) = star B * star A := by
    change ContinuousLinearMap.adjoint (A ∘L B) =
      (ContinuousLinearMap.adjoint B) ∘L
        (ContinuousLinearMap.adjoint A)
    exact ContinuousLinearMap.adjoint_comp A B
  calc
    originalFockCliffordAlgHom (star (x * y)) =
        originalFockCliffordAlgHom (star y * star x) := by
          rw [star_mul]
    _ = originalFockCliffordAlgHom (star y) *
          originalFockCliffordAlgHom (star x) := by
            rw [map_mul]
    _ = star (originalFockCliffordAlgHom y) *
          star (originalFockCliffordAlgHom x) := by
            rw [hx, hy]
    _ = star (originalFockCliffordAlgHom x *
          originalFockCliffordAlgHom y) := by
            exact (hadj _ _).symm
    _ = star (originalFockCliffordAlgHom (x * y)) := by
          rw [map_mul]

#print axioms originalFockCliffordAlgHom_star_mul_of

end
end FCP.BFSSS1V52L9E5F1
