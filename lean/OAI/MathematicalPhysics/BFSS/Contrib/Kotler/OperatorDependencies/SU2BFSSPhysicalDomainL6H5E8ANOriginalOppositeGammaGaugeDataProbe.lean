import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8ADOppositeGammaOrientationProbe
import OAI.MathematicalPhysics.BFSS.GaugeCore

/-!
# H5E8AN — original source SU2 gauge data under opposite gamma orientation

The qualified AD structure changes only gamma and its evidence.
The actual original source GaugeData record depends on the source
color basis and theta fields (through boson_adjoint and fermion_adjoint),
but NOT on nine-dimensional Clifford gamma orientation.

Make the dependent transport explicit and test whether the original
gauge-space/core definitions are definitionally identical — no
fabricated gauge group representation, no new hypotheses, and no
transport of the *charge graph* until the exact source test compiles.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AN
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AD

/-- Reuse the actual same source gauge boson and Fock fermion
representation for the valid opposite-gamma AlgebraData. -/
noncomputable def originalOppositeGammaGaugeData {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    (oppositeGamma M).GaugeData where
  boson := G.boson
  fermion := G.fermion
  boson_adjoint := by
    intro g x i
    exact G.boson_adjoint g x i
  fermion_adjoint := by
    intro g α A f
    exact G.fermion_adjoint g α A f
  boson_continuous := G.boson_continuous
  fermion_continuous := G.fermion_continuous

/-- The exact original source gauge physical Hilbert spaces agree;
no new physical state constraint is introduced by gamma reversal. -/
theorem originalOppositeGammaGaugeData_physicalSpace {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    (originalOppositeGammaGaugeData M G).physicalSpace =
      G.physicalSpace := rfl

/-- The literal original invariant SmoothCore is also unchanged,
so its restricted graph and all sixteen charges can be compared
on an identical source input domain. -/
theorem originalOppositeGammaGaugeData_invariantCore {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    (originalOppositeGammaGaugeData M G).invariantCore =
      G.invariantCore := rfl

#print axioms originalOppositeGammaGaugeData
#print axioms originalOppositeGammaGaugeData_physicalSpace
#print axioms originalOppositeGammaGaugeData_invariantCore

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AN
