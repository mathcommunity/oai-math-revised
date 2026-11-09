import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52M3FOriginalCliffordFockFiniteDimensionsProbe
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
M3G — source-exact complex finrank of ACTUAL 24-mode Fock bounded
endomorphisms, then equality with accepted source complex Clifford
algebra rank.

This uses a genuine continuous-linear equivalence from ALL algebraic
linear endomorphisms of the original finite-dimensional Fock Hilbert
space to ALL continuous-linear endomorphisms. In particular the target
is *not* replaced by an arbitrary matrix or abstract finite module.

M3D original full-image SURJECTIVITY plus the two equal source and
target dimensions would support a *later* source-actual INJECTIVITY
proof. Neither is claimed in this candidate. No independent
manuscript-module unitary and no unbounded BFSS physics are inferred.

UNQUALIFIED research source until strict compile and allowed-axiom
reports succeed; three original allowed axioms only.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52M3G
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V52M3F

private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- The ACTUAL original 24-complex-mode Fock endomorphism algebra
is 2^48-dimensional over ℂ, counting all bounded ℂ-linear maps. -/
theorem originalFockContinuousEnd_finrank :
    Module.finrank ℂ FockOp = 2 ^ 48 := by
  calc
    Module.finrank ℂ FockOp =
        Module.finrank ℂ (Fermion 2 →ₗ[ℂ] Fermion 2) :=
      (LinearMap.toContinuousLinearMap :
        (Fermion 2 →ₗ[ℂ] Fermion 2) ≃ₗ[ℂ] FockOp).finrank_eq.symm
    _ = Module.finrank ℂ (Fermion 2) *
          Module.finrank ℂ (Fermion 2) := by
      rw [Module.finrank_linearMap]
    _ = 2 ^ 48 := by
      rw [originalFock_finrank, ← pow_add]

/-- The ACTUAL base-changed original Clifford algebra and the
ACTUAL full continuous-linear source Fock endomorphism algebra have
the SAME complex dimension, computed without enumerating 2^48 basis
elements. This is only a dimension equality, not faithfulness. -/
theorem originalCliffordFock_finrank_eq :
    Module.finrank ℂ
        (CliffordAlgebra (source48Quadratic.baseChange ℂ)) =
      Module.finrank ℂ FockOp := by
  rw [originalComplexClifford_finrank_pow,
    originalFockContinuousEnd_finrank]

#print axioms originalFockContinuousEnd_finrank
#print axioms originalCliffordFock_finrank_eq

end
end FCP.BFSSS1V52M3G
