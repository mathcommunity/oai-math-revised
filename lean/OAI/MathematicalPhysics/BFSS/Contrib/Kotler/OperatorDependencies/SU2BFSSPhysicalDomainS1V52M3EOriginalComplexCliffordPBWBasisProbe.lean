import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52L9E5F20BOriginalSource48CliffordPBWBasisFiniteDimensionalProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.Free

/-!
M3E — original source COMPLEX 48-Clifford PBW basis, following
M3D strict acceptance of full-image surjectivity.

Transport the already STRICT-ACCEPTED ORIGINAL real source PBW basis
through Mathlib's exact quadratic-form Clifford base-change algebra
equivalence. This isolates dimension/faithfulness groundwork rather
than re-proving the underlying Clifford PBW theorem.

Research candidate ONLY: never count a theorem or basis definition
until compilation, source pinning and strict axiom reports pass.
M3D surjectivity does not by itself give injectivity; the
independent manuscript-module unitary is still unconstructed.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52M3E
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V52L9E5F20B
open scoped TensorProduct

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev A := CliffordAlgebra (Q.baseChange ℂ)

/-- Complex PBW basis of the ACTUAL base-changed original 48-Clifford
algebra, transported from the qualified real source basis. -/
noncomputable def originalComplexCliffordPBWBasis :
    Module.Basis (Finset Source48Label) ℂ A := by
  classical
  let e : (ℂ ⊗[ℝ] CliffordAlgebra Q) ≃ₗ[ℂ] A :=
    (CliffordAlgebra.equivBaseChange ℂ Q).toLinearEquiv.symm
  exact (originalSourceCliffordPBWBasis.baseChange ℂ).map e

/-- Source complex Clifford dimension, explicitly the number of
subsets of the *original* Source48Label, no abstract Clifford surrogate. -/
theorem originalComplexClifford_finrank :
    Module.finrank ℂ A = Fintype.card (Finset Source48Label) := by
  classical
  letI : FiniteDimensional ℂ A :=
    originalComplexCliffordPBWBasis.finiteDimensional_of_finite
  exact Module.finrank_eq_card_basis originalComplexCliffordPBWBasis

#print axioms originalComplexCliffordPBWBasis
#print axioms originalComplexClifford_finrank

end
end FCP.BFSSS1V52M3E
