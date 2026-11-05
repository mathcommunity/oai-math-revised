import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9C2OriginalNormalizedPauliQuaternionTraceProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52C2CNativeSU2RealQuaternionMatrixBridgeProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG3AAdjointColorRepresentationProbe

/-!
S1V52L9C3 — STAGED, UNQUALIFIED pinned original native BFSS SU2
color action matrix versus the actual original source Clifford
quaternion coefficient matrix.

The original upstream AlgebraData.adjointCoefficient is a real trace
of pairedAlgebraData.color B * (g * color A * g†), and the actual G3A
adjointColorMatrix g B A is that source coefficient with B=output,
A=input. Unlike earlier finite-only L9C1/L9C2 this module explicitly
states the ORIGINAL native source theorem. This requires separately
qualified source imports of actual G3A, G1A and the native quaternion
whole matrix reconstruction.

No assertions of full Spin48 projection, sixteen-block assembly,
continuity, Fock intertwiner, Hamiltonian or spectral positivity.

UNQUALIFIED until L9C1 and L9C2 pass their own strict gates, then
qualified pinned G3A/G1A closure and independent Lean axiom reports.
-/
set_option autoImplicit false
set_option maxHeartbeats 380000

namespace FCP.BFSSS1V52L9C3
noncomputable section

open Matrix
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG3A
open FCP.BFSSS1V52C1
open FCP.BFSSS1V52C2C
open FCP.BFSSS1V52L9C1
open FCP.BFSSS1V52L9C2

/-- Exact ORIGINAL paired-AlgebraData trace coefficients equal source
quaternion adjoint coefficients in output-row/input-column order. -/
theorem originalNativePairedAdjointCoefficient_eq_quaternion
    (g : GaugeGroup 2) (A B : ColorIndex 2) :
    pairedAlgebraData.adjointCoefficient g A B =
      originalQuaternionAdjointPolynomial (originalNativeQuaternionCoords g) B A := by
  unfold OAI.BFSSQuantum.AlgebraData.adjointCoefficient
  simp only [pairedAlgebraData_color,
    FCP.BFSSSU2Full.concreteAlgebraData_color]
  rw [← originalNativeQuaternion_matrix_reconstruction g]
  rw [originalNormalizedPauli_quaternion_trace_polynomial]
  simp

/-- Native REAL 3x3 matrix from the actual pinned BFSS AlgebraData
equals the source quaternion Clifford polynomial, with exact original
G3A row=output, column=input indexing. -/
theorem originalNativeAdjointColorMatrix_eq_quaternion
    (g : GaugeGroup 2) (B A : ColorIndex 2) :
    adjointColorMatrix g B A =
      originalQuaternionAdjointPolynomial (originalNativeQuaternionCoords g) B A := by
  exact originalNativePairedAdjointCoefficient_eq_quaternion g A B

#print axioms originalNativePairedAdjointCoefficient_eq_quaternion
#print axioms originalNativeAdjointColorMatrix_eq_quaternion

end
end FCP.BFSSS1V52L9C3
