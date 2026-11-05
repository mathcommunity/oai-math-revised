import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F2OriginalFiniteBivectorWordFockStarAdjointProbe

/-!
S1V52L9E5F3 — STAGED ONLY / UNQUALIFIED.
Exact original Clifford algebra and exact Fermion 2 operator:
  rho : CliffordAlgebra source48Quadratic →ₐ[ℝ]
    (Fermion 2 →L[ℂ] Fermion 2).

The source Clifford star on real vectors is NEGATIVE; rho
does not preserve star on arbitrary ODD elements. Here we
prove only the compatibility predicate for ZERO, and closure
of the predicate under ADDITION PROVIDED IT HOLDS ON BOTH
SUMMANDS. No global star-algebra map is constructed.

In the original Fock operator algebra, use the pinned typed
ContinuousLinearMap.adjoint equivalence for sum additivity.
The earlier E2 red gates showed generic IsSelfAdjoint.add
and Fock-side star_add can pick a wrong inferred star instance.

These two roots are prerequisites for compatibility on finite
real linear combinations of F2 original bivector words.
-/

set_option autoImplicit false
set_option maxHeartbeats 320000

namespace FCP.BFSSS1V52L9E5F3
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5F2

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- The actual original Fock Clifford algebra realization
preserves star at the source ZERO. -/
theorem originalFockCliffordAlgHom_star_zero :
    originalFockCliffordAlgHom (star (0 : C)) =
      star (originalFockCliffordAlgHom (0 : C)) := by
  -- Gate #1 left 0 = star 0 because the generic star_zero
  -- rewrite did not target the actual original Fock adjoint.
  simp only [star_zero, map_zero]
  change (0 : FockOp) =
    ContinuousLinearMap.adjoint (0 : FockOp)
  exact (map_zero (ContinuousLinearMap.adjoint :
    FockOp ≃ₗᵢ⋆[ℂ] FockOp)).symm

/-- Compatibility with source Clifford star and the actual
Fock Hilbert adjoint is additive IF each summand is compatible.
It does not hold on all odd source Clifford elements. -/
theorem originalFockCliffordAlgHom_star_add_of
    (x y : C)
    (hx : originalFockCliffordAlgHom (star x) =
      star (originalFockCliffordAlgHom x))
    (hy : originalFockCliffordAlgHom (star y) =
      star (originalFockCliffordAlgHom y)) :
    originalFockCliffordAlgHom (star (x + y)) =
      star (originalFockCliffordAlgHom (x + y)) := by
  have hadj (A B : FockOp) :
      star (A + B) = star A + star B := by
    change ContinuousLinearMap.adjoint (A + B) =
      (ContinuousLinearMap.adjoint A) +
        (ContinuousLinearMap.adjoint B)
    exact map_add
      (ContinuousLinearMap.adjoint :
        FockOp ≃ₗᵢ⋆[ℂ] FockOp) A B
  calc
    originalFockCliffordAlgHom (star (x + y)) =
        originalFockCliffordAlgHom (star x + star y) := by
          rw [star_add]
    _ = originalFockCliffordAlgHom (star x) +
          originalFockCliffordAlgHom (star y) := by
            rw [map_add]
    _ = star (originalFockCliffordAlgHom x) +
          star (originalFockCliffordAlgHom y) := by
            rw [hx, hy]
    _ = star (originalFockCliffordAlgHom x +
          originalFockCliffordAlgHom y) := by
            exact (hadj _ _).symm
    _ = star (originalFockCliffordAlgHom (x + y)) := by
          rw [map_add]

#print axioms originalFockCliffordAlgHom_star_zero
#print axioms originalFockCliffordAlgHom_star_add_of

end
end FCP.BFSSS1V52L9E5F3
