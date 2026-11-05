import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L1CIsolatedSource48CoordinateNormProbe

/-!
S1V52L1D — isolate genuine ORIGINAL Z-plane axis norm in a SMALL
two-root source gate. Reuse independently accepted L1C coordinate Q
and accepted S1V5 source-label injectivity, rather than specializing
generic QuadraticMap.map_add under concrete weightedSumSquares.

This does NOT assert source quaternion Lipschitz/Spin membership.
No source dimension, Clifford convention or gauge ordering is changed.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000

namespace FCP.BFSSS1V52L1D
noncomputable section
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L1C

/-- Distinct colors in the SAME actual source real-spin block label
distinct actual 48-coordinate Majorana labels. -/
theorem sourceBlockColorLabel_ne_of_color_ne
    (α : RealSpinBlock) (A B : ColorLabel) (hAB : A ≠ B) :
    sourceBlockColorLabel α A ≠ sourceBlockColorLabel α B := by
  intro h
  have hp : (α, A) = (α, B) :=
    sourceBlockColorLabel_injective h
  exact hAB (congrArg Prod.snd hp)

/-- The literal original source Z-plane vector has Q-norm one for
circle coefficients; no generic form substitution or surrogate
source model, and no nested concrete quadratic elaboration. -/
theorem sourceZPlane_firstVector_unit
    (α : RealSpinBlock) (c s : ℝ)
    (hcs : c*c+s*s=1) :
    source48Quadratic
      (c • sourceBlockColorAxis α 0 -
       s • sourceBlockColorAxis α 1) = 1 := by
  have hlabels :
      sourceBlockColorLabel α 0 ≠ sourceBlockColorLabel α 1 :=
    sourceBlockColorLabel_ne_of_color_ne α 0 1 (by decide)
  have hvector :
      c • sourceBlockColorAxis α 0 -
        s • sourceBlockColorAxis α 1 =
      c • (Pi.single (sourceBlockColorLabel α 0) (1 : ℝ) : Source48Vector) -
        s • (Pi.single (sourceBlockColorLabel α 1) (1 : ℝ) : Source48Vector) := by
    rfl
  calc
    source48Quadratic
        (c • sourceBlockColorAxis α 0 -
         s • sourceBlockColorAxis α 1) =
      source48Quadratic
        (c • (Pi.single (sourceBlockColorLabel α 0) (1 : ℝ) : Source48Vector) -
         s • (Pi.single (sourceBlockColorLabel α 1) (1 : ℝ) : Source48Vector)) :=
      congrArg (fun v : Source48Vector => source48Quadratic v) hvector
    _ = c*c+s*s :=
      source48Quadratic_two_coordinate_norm _ _ hlabels c s
    _ = 1 := hcs

#print axioms sourceBlockColorLabel_ne_of_color_ne
#print axioms sourceZPlane_firstVector_unit
end
end FCP.BFSSS1V52L1D
