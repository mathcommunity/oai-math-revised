import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52M3GOriginalFockContinuousOperatorFinrankProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52M3DOriginalComplexCliffordFullFockImageProbe
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
M3H — candidate exact original Clifford-to-Fock operator FAITHFULNESS.

The input M3D is the strictly accepted Jacobson-density/full-image
surjectivity theorem about the actual original complex 48-Clifford
action. M3E supplies a strictly accepted original complex Clifford
PBW basis, establishing source finite dimensionality; M3F accepts the
exact source Clifford rank and original 24-complex-mode Fock rank.

M3G equality of the Clifford rank and actual continuous-linear Fock
endomorphism rank is NOT accepted until M3G independently passes its
strict gate. This source intentionally contains no axiom/sorry and no
unproved hypothesis, but this M3H declaration is purely prospective.

Dimension equality + full-image surjectivity imply actual
injectivity of the very same original Clifford algebra homomorphism.
This does not construct an INDEPENDENT manuscript Hilbert module,
intertwiner, unitary, Spin(48) realization, operator domains or BFSS
spectrum. No merge to main.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52M3H
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V52M2
open FCP.BFSSS1V52M3E
open FCP.BFSSS1V52M3G

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev A := CliffordAlgebra (Q.baseChange ℂ)
private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- Injectivity of the ACTUAL original-source complex Clifford
representation on the ACTUAL source Fock continuous operator algebra. -/
theorem originalComplexCliffordFock_injective :
    Function.Injective
      (originalComplexCliffordFockAlgHom : A →ₐ[ℂ] FockOp) := by
  let : FiniteDimensional ℂ A :=
    originalComplexCliffordPBWBasis.finiteDimensional_of_finite
  have hsurj : Function.Surjective
      ((originalComplexCliffordFockAlgHom :
          A →ₐ[ℂ] FockOp).toLinearMap) :=
    FCP.BFSSS1V52M3D.originalComplexCliffordFock_fullImage
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      originalCliffordFock_finrank_eq).2 hsurj

#print axioms originalComplexCliffordFock_injective

end
end FCP.BFSSS1V52M3H
