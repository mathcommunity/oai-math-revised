import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9TypedLinearMapProbe
import Mathlib.Algebra.Module.BigOperators

/-!
K1D18V9A — source-native matrix-unit evaluation for the accepted
typed real coefficient LinearMap, across native SpaceIndex and
original paired Source48Label carriers.

The sum over ordered spatial pairs has the factor (1/2:ℝ).
On a single matrix unit E_rs the evaluation must be exactly
(1/2) • H_rs. This is not yet evaluation on F_rs=E_rs-E_sr.

Proof uses Mathlib's pinned native Matrix.single and finite selector
sum, not a guessed 9-to-48 basis conversion. No arbitrary Lie
bracket preservation or group lift is inferred.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open scoped BigOperators

/-- Exact real-linear coefficient map on a source-native 9×9
matrix unit: its output is half of the matching original
paired-Fock normalized generator. -/
theorem coordinateToPairedLinearMap_matrixUnit
    (r s : SpaceIndex) :
    coordinateToPairedLinearMap
      (Matrix.single r s (1 : ℝ) : Matrix SpaceIndex SpaceIndex ℝ) =
      (1 / 2 : ℝ) • normalizedPairedPlane r s := by
  rw [coordinateToPairedLinearMap_apply]
  unfold coordinateToPairedFiniteLift
  congr 1
  -- The outer sum has only row r; the inner sum has only column s.
  -- Use exact single-support obligations instead of a global ite simp.
  rw [Finset.sum_eq_single r]
  · rw [Finset.sum_eq_single s]
    · simp
    · intro y _ hy
      simp [hy.symm]
    · simp
  · intro x _ hx
    simp [hx.symm]
  · simp

#print axioms coordinateToPairedLinearMap_matrixUnit

end
end FCP.BFSSPairedSpin9Plane
