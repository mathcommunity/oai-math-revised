import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52C2BNativeSU2QuaternionWholeMatrixSourceProbe

/-!
S1V52-C2C: candidate exact matrix equality between (i) the actual
original GaugeGroup 2 matrix and (ii) its accepted real quaternion
coordinates through the accepted B1 source-positive-i 2×2 matrix.

This uses real re/im of the genuine source 0,0 and 0,1 entries,
and C2B's exact original SU2 lower row. No surrogate group or source
sign changes. Neither C2A nor C2B is accepted until its own strict
CI green; this file is staged source only and must not be promoted.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000

namespace FCP.BFSSS1V52C2C
noncomputable section
open OAI.BFSSQuantum
open Matrix
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52C1
open FCP.BFSSS1V52C2B

/-- Conjugation of source complex entries in real coordinates,
retaining the original positive-i Pauli quaternion convention. -/
theorem sourceComplex_star_re_im (z : ℂ) :
    star z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

/-- The B1 quaternion matrix of the extracted native gauge coordinates
is literally the native original 2x2 source gauge matrix. -/
theorem originalNativeQuaternion_matrix_reconstruction
    (g : GaugeGroup 2) :
    sourceQuaternionColorMatrix (originalNativeQuaternionCoords g) =
      (g : ColorMatrix 2) := by
  let u : ℂ := (g : ColorMatrix 2) 0 0
  let v : ℂ := (g : ColorMatrix 2) 0 1
  calc
    sourceQuaternionColorMatrix (originalNativeQuaternionCoords g) =
        !![u,v; -star v,star u] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            (simp [sourceQuaternionColorMatrix, originalNativeQuaternionCoords,
              u, v, sourceComplex_star_re_im, Complex.re_add_im];
            ring)
    _ = (g : ColorMatrix 2) := by
      simpa only [u, v] using
        (originalNativeSU2_wholeQuaternionMatrix g).symm

#print axioms sourceComplex_star_re_im
#print axioms originalNativeQuaternion_matrix_reconstruction

end
end FCP.BFSSS1V52C2C
