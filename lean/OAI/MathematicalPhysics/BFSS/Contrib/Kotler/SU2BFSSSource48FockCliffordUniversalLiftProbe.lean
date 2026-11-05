import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSSource48AllVectorFockCliffordSquareProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

/-!
# Original Source48 Clifford universal lift into the actual Fock operators

EXPLORATORY PORT — NOT STRICT-QUALIFIED.

This candidate adapts FCP S1V52L9E5C1, whose original source blob is
91313c5e622577fd12fa4ce7ec59f457a816ae3a, to the exact Source48
definitions and real-linear Fock map on the community-aligned owner branch.
The only parent theorem is the separate original Source48 all-vector square;
its strict acceptance must be checked independently before this is admitted.

In particular, this probes whether the genuine Fermion 2 complex-linear
continuous operator algebra has the exact real Algebra instance needed by
CliffordAlgebra.lift.  Do not bypass failed elaboration with a surrogate
operator algebra, an additional axiom, or a change to the source quadratic form.

No Spin(48) kernel or covering assertion, global Spin(9) physical lift,
or BFSS spectral/existence claim follows from this staged representation.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSSource48FockCliffordUniversalLift
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSSource48RealLinearGamma
open FCP.BFSSSource48AllVectorFockCliffordSquare

private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- The original real Source48 Clifford algebra maps to the actual original
complex-linear Fock operators, provided the genuine real-algebra interface
elaborates. This is NOT accepted without a fresh strict Lean gate. -/
noncomputable def sourceFockCliffordAlgHom :
    CliffordAlgebra source48Quadratic →ₐ[ℝ] FockOp := by
  let f : Source48Vector →ₗ[ℝ] FockOp := sourceGammaRealLinear
  have hq (v : Source48Vector) :
      f v * f v =
        algebraMap ℝ FockOp (source48Quadratic v) := by
    change sourceGammaRealLinear v * sourceGammaRealLinear v =
      algebraMap ℝ FockOp (source48Quadratic v)
    calc
      sourceGammaRealLinear v * sourceGammaRealLinear v =
          (source48Quadratic v) • (1 : FockOp) :=
        sourceGammaRealLinear_sq v
      _ = algebraMap ℝ FockOp (source48Quadratic v) := by
        exact
          (Algebra.algebraMap_eq_smul_one
            (source48Quadratic v) :
              algebraMap ℝ FockOp (source48Quadratic v) =
                (source48Quadratic v) • (1 : FockOp)).symm
  exact CliffordAlgebra.lift source48Quadratic ⟨f, hq⟩

/-- The universal map agrees with the actual Source48 normalized Fock
Majorana linear combination on each original real source vector. -/
theorem sourceFockCliffordAlgHom_generator (v : Source48Vector) :
    sourceFockCliffordAlgHom
      (CliffordAlgebra.ι source48Quadratic v) =
        sourceGammaRealLinear v := by
  unfold sourceFockCliffordAlgHom
  rw [CliffordAlgebra.lift_ι_apply]

#print axioms sourceFockCliffordAlgHom
#print axioms sourceFockCliffordAlgHom_generator

end
end FCP.BFSSSource48FockCliffordUniversalLift
