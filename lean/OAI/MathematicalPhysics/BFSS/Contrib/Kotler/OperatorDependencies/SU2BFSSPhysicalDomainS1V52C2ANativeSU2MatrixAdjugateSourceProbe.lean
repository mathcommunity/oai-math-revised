import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52C1OriginalNativeGaugeQuaternionCoordinatesProbe
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
S1V52-C2A: exact source SU(2) native 2x2 quaternion MATRIX reconstruction
precondition. Deliberately mirrors the strictly previously accepted
L6H5E8P Original SU2 Unitary Quaternion Matrix Form proofs, but
compiles from the small C1 + genuine pinned BFSS Core import closure.

Theorems involve the REAL upstream OAI.BFSSQuantum.GaugeGroup 2, not a
surrogate group. They are candidates until the pinned strict CI passes.
Preserve source positive-i signs and the original index order.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSS1V52C2A
noncomputable section
open OAI.BFSSQuantum
open Matrix

/-- Native SU2 determinant-one and source unitarity imply
the exact 2x2 adjugate equals the Hermitian adjoint. -/
theorem originalNativeSU2_adjugate_eq_conjTranspose
    (g : GaugeGroup 2) :
    Matrix.adjugate (g : ColorMatrix 2) =
      (g : ColorMatrix 2)ᴴ := by
  let A : ColorMatrix 2 := g
  have hd : Matrix.det A = 1 := g.property.2
  have hu : Aᴴ * A = (1 : ColorMatrix 2) := by
    have hm : A ∈ Matrix.unitaryGroup (Fin 2) ℂ := g.property.1
    simpa only [Matrix.star_eq_conjTranspose] using hm.1
  have ha : A * Matrix.adjugate A = (1 : ColorMatrix 2) := by
    simpa only [hd, one_smul] using Matrix.mul_adjugate A
  change Matrix.adjugate A = Aᴴ
  calc
    Matrix.adjugate A = 1 * Matrix.adjugate A := (one_mul _).symm
    _ = (Aᴴ * A) * Matrix.adjugate A := by rw [hu]
    _ = Aᴴ * (A * Matrix.adjugate A) := by rw [mul_assoc]
    _ = Aᴴ := by rw [ha, mul_one]

/-- Native SU2 lower-right entry is the complex conjugate of upper-left. -/
theorem originalNativeSU2_bottomRight_eq_conj_topLeft
    (g : GaugeGroup 2) :
    ((g : ColorMatrix 2) 1 1) =
      star ((g : ColorMatrix 2) 0 0) := by
  have he := congrArg
    (fun A : ColorMatrix 2 => A 0 0)
    (originalNativeSU2_adjugate_eq_conjTranspose g)
  simpa [Matrix.adjugate_fin_two] using he

/-- Native SU2 lower-left entry has the exact source negative-conjugate
sign, preserving the original positive-i quaternion basis. -/
theorem originalNativeSU2_bottomLeft_eq_neg_conj_topRight
    (g : GaugeGroup 2) :
    ((g : ColorMatrix 2) 1 0) =
      -star ((g : ColorMatrix 2) 0 1) := by
  have he := congrArg
    (fun A : ColorMatrix 2 => A 1 0)
    (originalNativeSU2_adjugate_eq_conjTranspose g)
  have hneg :
      -((g : ColorMatrix 2) 1 0) =
        star ((g : ColorMatrix 2) 0 1) := by
    simpa [Matrix.adjugate_fin_two] using he
  calc
    ((g : ColorMatrix 2) 1 0) =
        -(-((g : ColorMatrix 2) 1 0)) := by simp
    _ = -star ((g : ColorMatrix 2) 0 1) := by rw [hneg]

#print axioms originalNativeSU2_adjugate_eq_conjTranspose
#print axioms originalNativeSU2_bottomRight_eq_conj_topLeft
#print axioms originalNativeSU2_bottomLeft_eq_neg_conj_topRight

end
end FCP.BFSSS1V52C2A
