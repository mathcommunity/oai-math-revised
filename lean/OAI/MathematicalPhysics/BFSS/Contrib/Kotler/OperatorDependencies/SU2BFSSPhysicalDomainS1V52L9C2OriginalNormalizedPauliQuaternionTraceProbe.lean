import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9C1OriginalPauliQuaternionTracePolynomialProbe

/-!
S1V52L9C2 — staged ORIGINAL normalized-Pauli 2x2 trace bridge.

Uses literally the source FCP.BFSSSU2.normalizedPauli, its accepted
pauliScale_sq=(1/2), exact native +i B1 quaternion color matrix, and
L9C1's original-Pauli trace polynomial. No separate Pauli basis,
alternative SU2 group, axiom, surrogate gauge action or spectral claim.

Still distinct: pairedAlgebraData.color and pinned native GaugeGroup2
adjointCoefficient, original color row/column matrix, 16 Spin blocks,
continuity and manuscript physical Fock/Hamiltonian interfaces.
UNQUALIFIED until L9C1 accepted and own strict pinned CI.
-/
set_option autoImplicit false
set_option maxHeartbeats 360000

namespace FCP.BFSSS1V52L9C2
noncomputable section

open Matrix
open FCP.BFSSSU2
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52L9C1

/-- The genuine original Pauli normalization appears exactly TWICE
in the trace, one factor for each source color generator. -/
theorem originalNormalizedPauli_trace_scale
    (p : SourceQuaternionCoords) (B A : Fin 3) :
    Matrix.trace
      (normalizedPauli B *
        (sourceQuaternionColorMatrix p * normalizedPauli A *
          (sourceQuaternionColorMatrix p).conjTranspose)) =
      ((pauliScale : ℂ) ^ 2) *
        Matrix.trace
          (pauli B *
            (sourceQuaternionColorMatrix p * pauli A *
              (sourceQuaternionColorMatrix p).conjTranspose)) := by
  simp only [normalizedPauli, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_smul, smul_eq_mul]
  ring

/-- The original normalized-Pauli trace is EXACTLY the real
nine-coefficient source quaternion adjoint polynomial. -/
theorem originalNormalizedPauli_quaternion_trace_polynomial
    (p : SourceQuaternionCoords) (B A : Fin 3) :
    Matrix.trace
      (normalizedPauli B *
        (sourceQuaternionColorMatrix p * normalizedPauli A *
          (sourceQuaternionColorMatrix p).conjTranspose)) =
      (originalQuaternionAdjointPolynomial p B A : ℂ) := by
  rw [originalNormalizedPauli_trace_scale,
    originalPauliQuaternion_trace_polynomial]
  have hs : ((pauliScale : ℂ) ^ 2) = (1/2 : ℂ) := by
    simpa using congrArg (fun x : ℝ => (x : ℂ)) pauliScale_sq
  rw [hs]
  push_cast
  ring

#print axioms originalNormalizedPauli_trace_scale
#print axioms originalNormalizedPauli_quaternion_trace_polynomial

end
end FCP.BFSSS1V52L9C2
