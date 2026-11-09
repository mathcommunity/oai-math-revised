import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8QOriginalSU2QuaternionUnitSphereProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6XOriginalSU2GaugeCurveProbe
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
L6H5E8R: FIRST exact source SU(2) Euler-generator interface.

Prove that the original positive-i z-color exponential is a diagonal
2x2 matrix, using the *actual* normalized Pauli color of the paired
48-Majorana BFSS AlgebraData and the pinned `Matrix.exp_diagonal`.

This is a restricted z-axis lemma ONLY. The y-axis closed form,
Euler-factorization witnesses and generated-subgroup equality remain open.
No new axioms, `sorry`, alternate gauge group, or Fock expression.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8R
noncomputable section
open Matrix
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2Full
open FCP.BFSSSU2PhysicalDomainL6G6V
open FCP.BFSSSU2PhysicalDomainL6G6X

/-- The original real-time +i normalization, with the exact Pauli
scale sqrt(2)/2, expressed as a diagonal vector. -/
noncomputable def sourceZDiagonal (t : ℝ) : Fin 2 → ℂ :=
  ![((t : ℂ) * Complex.I * (FCP.BFSSSU2.pauliScale : ℂ)),
    -((t : ℂ) * Complex.I * (FCP.BFSSSU2.pauliScale : ℂ))]

/-- The *actual* pairedAlgebraData +i z-tangent is diagonal.
This proves an exact matrix equality, not merely equality modulo
an alternate Lie-algebra basis or conjugation. -/
theorem source_z_tangent_diagonal (t : ℝ) :
    t • ((Complex.I : ℂ) • pairedAlgebraData.color (2 : Fin 3)) =
      Matrix.diagonal (sourceZDiagonal t) := by
  rw [pairedAlgebraData_color, concreteAlgebraData_color]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceZDiagonal, FCP.BFSSSU2.normalizedPauli,
      FCP.BFSSSU2.pauli, Matrix.smul_apply] <;> ring

/-- Pinned Mathlib diagonal-exponential identity, specialized to the
literal positive-i source gauge curve. All exponentials have the
original real-time parameter and original Pauli normalization. -/
theorem source_z_gaugeCurve_diagonal_exp (t : ℝ) :
    (sourcePlusIGaugeCurve (2 : Fin 3) t : ColorMatrix 2) =
      Matrix.diagonal (fun i => Complex.exp (sourceZDiagonal t i)) := by
  calc
    (sourcePlusIGaugeCurve (2 : Fin 3) t : ColorMatrix 2) =
        NormedSpace.exp (Matrix.diagonal (sourceZDiagonal t)) := by
          change NormedSpace.exp
            (t • ((Complex.I : ℂ) • pairedAlgebraData.color (2 : Fin 3))) = _
          rw [source_z_tangent_diagonal]
    _ = Matrix.diagonal (fun i => NormedSpace.exp (sourceZDiagonal t i)) := by
      -- Pinned Matrix.exp_diagonal returns exp on the function space;
      -- Pi.exp_def discharges the required pointwise scalar transport.
      rw [Matrix.exp_diagonal, Pi.exp_def]
    _ = Matrix.diagonal (fun i => Complex.exp (sourceZDiagonal t i)) := by
      simp only [Complex.exp_eq_exp_ℂ]

#print axioms sourceZDiagonal
#print axioms source_z_tangent_diagonal
#print axioms source_z_gaugeCurve_diagonal_exp
#check @source_z_gaugeCurve_diagonal_exp

end
end FCP.BFSSSU2PhysicalDomainL6H5E8R
