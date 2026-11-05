import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V0StandaloneOrthogonalGeometryProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Owner FCP source-only port, original cc608e2282e1b32bb11bbb64424e4775b28138e2; Git blob 6e4c78fd31f9781267659313a8a0edfedd65e9ad.
Imports alone have been restructured; theorem statements/proof bodies unchanged.
The omitted original Spin ancestry is not claimed qualified by this port.
Status: provisional pending fresh owner strict-gate acceptance. -/

/-!
S1V52-L9E5F20B — source-exact 48-real Clifford PBW basis and real finite dimensionality.

The pinned original source has Source48Label := Fin 24 × Fin 2,
Source48Vector := Source48Label → ℝ, and source48Quadratic.
Pinned Mathlib's CliffordAlgebra.equivExterior supplies a REAL-linear
equivalence, not an algebra equivalence, to the actual exterior algebra;
the actual function-coordinate Pi.basisFun has an exterior basis
indexed by Finset Source48Label. Transport this basis back to
the ACTUAL original source CliffordAlgebra source48Quadratic.

This is a prerequisite for the natural finite-dimensional real
topology. It is NOT an instance of a topological algebra or a
continuous Spin48-valued lift. In particular do NOT assume the
equivExterior map is multiplicative: it is only real linear.

Prospective until strict source-pinned Lean compilation and
permitted #print axioms succeed; no independence, domains, spectrum.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52L9E5F20B
noncomputable section

open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Actual Clifford PBW-style REAL basis, transported from the
source 48-coordinate exterior basis via pinned Mathlib's
real-linear Clifford/exterior equivalence. -/
noncomputable def originalSourceCliffordPBWBasis :
    Module.Basis (Finset Source48Label) ℝ C := by
  classical
  letI : LinearOrder Source48Label := linearOrderOfSTO WellOrderingRel
  exact ((Pi.basisFun ℝ Source48Label).ExteriorAlgebra).map
    (CliffordAlgebra.equivExterior Q).symm

/-- The ACTUAL source 48-real Clifford algebra is finite-dimensional
as an ℝ-vector space. This statement is independent of arbitrary
topology choices or assumptions about a Spin lifting theorem. -/
theorem originalSourceClifford_finiteDimensional :
    FiniteDimensional ℝ C :=
  originalSourceCliffordPBWBasis.finiteDimensional_of_finite

#print axioms originalSourceCliffordPBWBasis
#print axioms originalSourceClifford_finiteDimensional

end
end FCP.BFSSS1V52L9E5F20B
