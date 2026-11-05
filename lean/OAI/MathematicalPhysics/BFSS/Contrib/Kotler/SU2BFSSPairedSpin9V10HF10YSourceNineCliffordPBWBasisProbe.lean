import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10XSourceCliffordGammaKernelCriterionProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
K1D18V10H-F10Y — source-exact NINE-real Clifford PBW basis.

The accepted F10X identifies exactly which original-source
even-Clifford gamma injectivity theorem remains necessary.
We reuse the *construction method* of accepted-source F20B
(the ORIGINAL 48-real Clifford PBW basis), but NOT its
48-label carrier, quadratic form, or any assumed spin lift.

The source is EXACTLY SpaceIndex := Fin 9 and the already
accepted source9Quadratic, with the original gamma representation
imported from accepted F10X ancestry.

CliffordAlgebra.equivExterior is an ℝ-LINEAR equivalence.
It is NOT a multiplicative algebra equivalence. This stage
constructs an indexed real PBW basis and its finite-dimensional
consequence only, not an algebra embedding or an even-image
matrix coefficient-separation result.

CANDIDATE pending pinned strict compiler and independent
declaration type/axiom verification. No raised limits.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum

/-- Exact actual source nine-real Clifford PBW ℝ-basis,
transported from its nine-coordinate exterior basis using
the pinned REAL-LINEAR Clifford/exterior equivalence. -/
noncomputable def source9CliffordPBWBasis :
    Module.Basis (Finset SpaceIndex) ℝ
      (CliffordAlgebra source9Quadratic) := by
  classical
  exact ((Pi.basisFun ℝ SpaceIndex).ExteriorAlgebra).map
    (CliffordAlgebra.equivExterior source9Quadratic).symm

/-- The ACTUAL source Clifford algebra Cl(source9Quadratic),
rather than the original 48-real Clifford algebra, is finite
dimensional over ℝ by its exact nine-label PBW basis. -/
theorem source9Clifford_finiteDimensional :
    FiniteDimensional ℝ (CliffordAlgebra source9Quadratic) :=
  source9CliffordPBWBasis.finiteDimensional_of_finite

#print axioms source9CliffordPBWBasis
#print axioms source9Clifford_finiteDimensional

end
end FCP.BFSSPairedSpin9Clifford
