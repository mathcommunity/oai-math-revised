import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7ERotatedThetaCommutatorEvolutionProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6ZOriginalColorFlowVacuumProbe

/-!
L6G7F — operator-level calculus for the literal source fermionic
color-current exponential V_c(t)=exp(t J_F(c)) on Fermion 2.

L6G7E has already qualified B'_A(t)=[J_F(c),B_A(t)].
This module isolates the remaining reusable *bounded operator*
exponential interfaces; it does not yet integrate that ODE.

Boundary: no identification with the original G4B gauge action,
no combined Gauss constraint, no BFSS spectrum statement.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace FCP.BFSSSU2PhysicalDomainL6G7F
noncomputable section

open scoped Topology
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2PhysicalDomainL6G6K
open FCP.BFSSSU2PhysicalDomainL6G6Z

local instance sourceFockRationalNormedAlgebra :
    NormedAlgebra ℚ SourceFiberEnd :=
  .restrictScalars ℚ ℂ SourceFiberEnd

/-- Literal original bounded fermion flow is inverse at negative time. -/
theorem sourceFermionColorFlow_mul_neg
    (c : ColorIndex 2) (t : ℝ) :
    sourceFermionColorFlow c t *
      sourceFermionColorFlow c (-t) = 1 := by
  rw [← sourceFermionColorFlow_add, add_neg_cancel,
    sourceFermionColorFlow_zero]

theorem sourceFermionColorFlow_neg_mul
    (c : ColorIndex 2) (t : ℝ) :
    sourceFermionColorFlow c (-t) *
      sourceFermionColorFlow c t = 1 := by
  rw [← sourceFermionColorFlow_add, neg_add_cancel,
    sourceFermionColorFlow_zero]

/-- The literal source skew generator commutes with its own norm
convergent exponential; the sign/orientation is unchanged. -/
theorem sourceFermionColorGenerator_commute_flow
    (c : ColorIndex 2) (t : ℝ) :
    Commute (sourceFiberFermionColorGenerator pairedAlgebraData c)
      (sourceFermionColorFlow c t) := by
  change Commute
    (sourceFiberFermionColorGenerator pairedAlgebraData c)
    (NormedSpace.exp ((t : ℂ) •
      sourceFiberFermionColorGenerator pairedAlgebraData c))
  exact ((Commute.refl
    (sourceFiberFermionColorGenerator pairedAlgebraData c)).smul_right
      (t : ℂ)).exp_right

/-- Operator-valued real derivative of the exact source exponential,
prior to applying the operator to a Fock vector. -/
theorem sourceFermionColorFlow_derivative_operator
    (c : ColorIndex 2) (t : ℝ) :
    HasDerivAt (fun u : ℝ => sourceFermionColorFlow c u)
      (sourceFermionColorFlow c t *
        sourceFiberFermionColorGenerator pairedAlgebraData c) t := by
  change HasDerivAt
    (fun u : ℝ => NormedSpace.exp
      (u • sourceFiberFermionColorGenerator pairedAlgebraData c))
    (NormedSpace.exp
      (t • sourceFiberFermionColorGenerator pairedAlgebraData c) *
        sourceFiberFermionColorGenerator pairedAlgebraData c) t
  exact hasDerivAt_exp_smul_const
    (sourceFiberFermionColorGenerator pairedAlgebraData c) t

#print axioms sourceFermionColorFlow_mul_neg
#print axioms sourceFermionColorFlow_neg_mul
#print axioms sourceFermionColorGenerator_commute_flow
#print axioms sourceFermionColorFlow_derivative_operator
#check @sourceFermionColorFlow_derivative_operator

end
end FCP.BFSSSU2PhysicalDomainL6G7F
