import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BEPBWTopologyGammaContinuity
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
F10BF — ambient source Clifford topological ring for the accepted PBW topology.

Candidate specialization of pinned Mathlib module-topology theorems.
Use precisely the accepted F10BE normed structures, locally. The module-
topology bridge concerns that existing topology; no topology is replaced.

Scope: module-topology identification, joint continuity of the existing
Clifford multiplication, and the ambient topological-ring structure.
No source Spin9 inverse-continuity or topological-group structure,
manifold, smoothness, differential comparison, Spin lift, Fock,
gauge-domain compatibility or spectral result is claimed.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum

local instance f10bfLocalNormedAddCommGroup : NormedAddCommGroup (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedAddCommGroup

local instance f10bfLocalNormedSpace : NormedSpace ℝ (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedSpace

local instance f10bfLocalFiniteDimensional : FiniteDimensional ℝ (CliffordAlgebra source9Quadratic) :=
  source9Clifford_finiteDimensional

/-- The existing accepted PBW-coordinate topology is the real module topology. -/
theorem source9Clifford_isModuleTopology_pbw :
    IsModuleTopology ℝ (CliffordAlgebra source9Quadratic) := by
  exact isModuleTopologyOfFiniteDimensional

local instance f10bfLocalIsModuleTopology : IsModuleTopology ℝ (CliffordAlgebra source9Quadratic) :=
  source9Clifford_isModuleTopology_pbw

/-- The actual Clifford multiplication is jointly continuous for the accepted PBW topology. -/
theorem source9Clifford_mul_continuous_pbw :
    Continuous (fun xy : CliffordAlgebra source9Quadratic × CliffordAlgebra source9Quadratic =>
      xy.1 * xy.2) := by
  exact IsModuleTopology.continuous_mul_of_finite ℝ (CliffordAlgebra source9Quadratic)

/-- The actual source Clifford ring, with the accepted PBW topology, is a topological ring. -/
theorem source9Clifford_isTopologicalRing_pbw :
    IsTopologicalRing (CliffordAlgebra source9Quadratic) := by
  exact IsModuleTopology.isTopologicalRing ℝ (CliffordAlgebra source9Quadratic)

#print axioms source9Clifford_isModuleTopology_pbw
#print axioms source9Clifford_mul_continuous_pbw
#print axioms source9Clifford_isTopologicalRing_pbw

end
end FCP.BFSSPairedSpin9Clifford
