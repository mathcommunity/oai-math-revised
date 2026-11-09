import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSSource48FockGammaSelfAdjointProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSSource48FockCliffordUniversalLiftProbe

/-!
# Source-exact Clifford bivector star versus actual Fock adjoint

STAGED RESEARCH CANDIDATE; no independent strict gate yet.

Adapted from FCP S1V52L9E5E3 original source
109baa5a4e0e3d5480a17dc4ca3a3a0526d4b333 with explicit Source48
identification and its actual original fermionic Fock Clifford map.

The source Clifford odd generator is star-NEGATIVE, while its normalized
Fock operator image is self-adjoint: the representation is NOT a global
star-homomorphism. This bounded lemma tests only star compatibility for a
product of two true original Clifford generators. Its parent all-real-vector
self-adjointness is still pending independent strict qualification. No
Spin(48) group-unitary or BFSS physical spectral assertion is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 320000

namespace FCP.BFSSSource48FockBivectorStar
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSSource48RealLinearGamma
open FCP.BFSSSource48FockCliffordUniversalLift
open FCP.BFSSSource48FockGammaSelfAdjoint

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Actual original Fock Clifford representation respects the source
Clifford star on degree-two products of original real generators.
This statement does not extend to odd generators or to all elements. -/
theorem sourceFockCliffordAlgHom_star_bivector
    (u v : Source48Vector) :
    sourceFockCliffordAlgHom
      (star (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v)) =
    star (sourceFockCliffordAlgHom
      (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v)) := by
  have hcl :
      star (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) =
        CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q u := by
    simp only [star_mul, CliffordAlgebra.star_ι, neg_mul_neg]
  calc
    sourceFockCliffordAlgHom
        (star (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v)) =
      sourceFockCliffordAlgHom
        (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q u) := by
          rw [hcl]
    _ = sourceGammaRealLinear v * sourceGammaRealLinear u := by
          rw [map_mul, sourceFockCliffordAlgHom_generator,
            sourceFockCliffordAlgHom_generator]
    _ = star (sourceGammaRealLinear u * sourceGammaRealLinear v) := by
          have hadj :
              ContinuousLinearMap.adjoint
                  (sourceGammaRealLinear u * sourceGammaRealLinear v) =
                sourceGammaRealLinear v * sourceGammaRealLinear u := by
            change ContinuousLinearMap.adjoint
                (sourceGammaRealLinear u ∘L sourceGammaRealLinear v) =
              sourceGammaRealLinear v ∘L sourceGammaRealLinear u
            rw [ContinuousLinearMap.adjoint_comp,
              (sourceGammaRealLinear_selfAdjoint v).adjoint_eq,
              (sourceGammaRealLinear_selfAdjoint u).adjoint_eq]
          exact (ContinuousLinearMap.star_eq_adjoint
            (sourceGammaRealLinear u * sourceGammaRealLinear v)).trans hadj |>.symm
    _ = star (sourceFockCliffordAlgHom
          (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v)) := by
            rw [map_mul, sourceFockCliffordAlgHom_generator,
              sourceFockCliffordAlgHom_generator]

#print axioms sourceFockCliffordAlgHom_star_bivector

end
end FCP.BFSSSource48FockBivectorStar

/-!
Independent contributor adaptation, 2026-10-27.
Original BFSS definitions remain attributed to their original OpenAI authors.
Copyright (c) 2026 Evan T. Kotler.
SPDX-License-Identifier: Apache-2.0.
-/
