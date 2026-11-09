import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52C2CNativeSU2RealQuaternionMatrixBridgeProbe

/-!
S1V52-C2D: RESEARCH CANDIDATE for exact multiplication of real
quaternion coordinates extracted from the genuinely native upstream
OAI.BFSSQuantum.GaugeGroup 2.

Dependencies: source exact C1 native original quaternion coordinates,
B1 real-coordinate 2x2 positive-i matrix product, C2B actual native
whole SU2 matrix, and staged C2C real-coordinate matrix reconstruction.
C2C is not yet accepted until its strict source-pinned CI gate goes green.
No different SU2 group, no +i sign changes, no unproved assumptions,
no spectral or global Spin claims. A source-only staging commit cannot
be counted as qualification for either theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000

namespace FCP.BFSSS1V52C2D
noncomputable section
open OAI.BFSSQuantum
open Matrix
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52C1
open FCP.BFSSS1V52C2C

/-- Extract real source quaternion coefficients from a complex 2x2
color matrix's literal first row. Works for arbitrary matrices, not
only SU2 matrices; this provides the left-inverse test. -/
def sourceQuaternionCoordsOfMatrix (M : ColorMatrix 2) :
    SourceQuaternionCoords :=
  ⟨(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im⟩

/-- The re/im first-row extraction is a left inverse to the original
size-2 positive-i quaternion-color matrix for every real quadruple. -/
theorem sourceQuaternionCoordsOfMatrix_sourceMatrix
    (p : SourceQuaternionCoords) :
    sourceQuaternionCoordsOfMatrix (sourceQuaternionColorMatrix p) = p := by
  cases p with
  | mk a b c d =>
    simp [sourceQuaternionCoordsOfMatrix, sourceQuaternionColorMatrix,
      Complex.mul_re, Complex.mul_im]

/-- Native original SU2 group multiplication is exactly the accepted
positive-i quaternion real-coordinate law, not a substitute SU2 law. -/
theorem originalNativeQuaternionCoords_mul
    (g h : GaugeGroup 2) :
    originalNativeQuaternionCoords (g * h) =
      sourceQuaternionCompose (originalNativeQuaternionCoords g)
        (originalNativeQuaternionCoords h) := by
  have hm :
      sourceQuaternionColorMatrix (originalNativeQuaternionCoords (g * h)) =
        sourceQuaternionColorMatrix
          (sourceQuaternionCompose
            (originalNativeQuaternionCoords g)
            (originalNativeQuaternionCoords h)) := by
    calc
      sourceQuaternionColorMatrix (originalNativeQuaternionCoords (g * h)) =
          ((g * h : GaugeGroup 2) : ColorMatrix 2) :=
        originalNativeQuaternion_matrix_reconstruction (g * h)
      _ = (g : ColorMatrix 2) * (h : ColorMatrix 2) := rfl
      _ = sourceQuaternionColorMatrix (originalNativeQuaternionCoords g) *
          sourceQuaternionColorMatrix (originalNativeQuaternionCoords h) := by
          rw [originalNativeQuaternion_matrix_reconstruction,
              originalNativeQuaternion_matrix_reconstruction]
      _ = sourceQuaternionColorMatrix
            (sourceQuaternionCompose (originalNativeQuaternionCoords g)
              (originalNativeQuaternionCoords h)) :=
        (sourceQuaternionColorMatrix_compose
          (originalNativeQuaternionCoords g)
          (originalNativeQuaternionCoords h)).symm
  have hcoords := congrArg sourceQuaternionCoordsOfMatrix hm
  simpa only [sourceQuaternionCoordsOfMatrix_sourceMatrix] using hcoords

#print axioms sourceQuaternionCoordsOfMatrix_sourceMatrix
#print axioms originalNativeQuaternionCoords_mul

end
end FCP.BFSSS1V52C2D
