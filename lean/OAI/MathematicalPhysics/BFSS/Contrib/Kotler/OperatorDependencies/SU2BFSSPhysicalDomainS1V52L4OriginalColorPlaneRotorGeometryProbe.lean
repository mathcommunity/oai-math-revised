import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L1DOriginalZPlaneSourceAxisUnitProbe

/-!
S1V52L4 — STAGED, UNQUALIFIED source-exact two-color plane geometry.

The accepted strict L1D result closes the fixed Z-plane. This gate
proposes a general two-color unit norm and exact two-ι Clifford
factorization for ANY distinct original color axes, with the same
original quadratic form and original positive-i bivector orientation.

It is intended to cover the genuine Y-plane (A=2,B=0), not to
introduce an independent three-dimensional surrogate.
This geometry module deliberately DOES NOT import L3 Spin membership.
No theorem is accepted until a separately pinned strict CI.
-/
set_option autoImplicit false
set_option maxHeartbeats 470000

namespace FCP.BFSSS1V52L4
noncomputable section
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52A
open FCP.BFSSS1V52L1D
open FCP.BFSSS1V52L1C

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Exact source 48-vector quadratic norm for arbitrary distinct
color axes within the same genuine original spin block. -/
theorem sourceColorPlane_firstVector_unit
    (α : RealSpinBlock) (A B : ColorLabel) (hAB : A ≠ B)
    (c s : ℝ) (hcs : c*c+s*s=1) :
    Q (c • sourceBlockColorAxis α A -
       s • sourceBlockColorAxis α B) = 1 := by
  have hlabels :
      sourceBlockColorLabel α A ≠ sourceBlockColorLabel α B :=
    sourceBlockColorLabel_ne_of_color_ne α A B hAB
  have hvector :
      c • sourceBlockColorAxis α A -
        s • sourceBlockColorAxis α B =
      c • (Pi.single (sourceBlockColorLabel α A) (1 : ℝ) : Source48Vector) -
        s • (Pi.single (sourceBlockColorLabel α B) (1 : ℝ) : Source48Vector) := by
    rfl
  calc
    Q (c • sourceBlockColorAxis α A -
       s • sourceBlockColorAxis α B) =
      Q (c • (Pi.single (sourceBlockColorLabel α A) (1 : ℝ) : Source48Vector) -
        s • (Pi.single (sourceBlockColorLabel α B) (1 : ℝ) : Source48Vector)) :=
      congrArg (fun v : Source48Vector => Q v) hvector
    _ = c*c+s*s :=
      source48Quadratic_two_coordinate_norm _ _ hlabels c s
    _ = 1 := hcs

/-- Exact original-source Clifford factorization in any oriented
color plane: this does NOT assert Spin membership by itself. -/
theorem sourceColorPlane_twoVector_factor
    (α : RealSpinBlock) (A B : ColorLabel) (hAB : A ≠ B)
    (c s : ℝ) :
    CliffordAlgebra.ι Q
      (c • sourceBlockColorAxis α A -
       s • sourceBlockColorAxis α B) *
      CliffordAlgebra.ι Q (sourceBlockColorAxis α A) =
      c • (1 : C) +
        s • (CliffordAlgebra.ι Q (sourceBlockColorAxis α A) *
             CliffordAlgebra.ι Q (sourceBlockColorAxis α B)) := by
  let a : Source48Vector := sourceBlockColorAxis α A
  let b : Source48Vector := sourceBlockColorAxis α B
  have hBA : B ≠ A := by
    intro h
    exact hAB h.symm
  have haa : CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q a = 1 :=
    sourceAxis_square α A
  have hba : CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q a =
      -(CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) :=
    sourceAxis_anticomm α B A hBA
  change CliffordAlgebra.ι Q (c • a - s • b) *
      CliffordAlgebra.ι Q a =
      c • (1 : C) + s •
        (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b)
  calc
    CliffordAlgebra.ι Q (c • a - s • b) *
        CliffordAlgebra.ι Q a =
      (c • CliffordAlgebra.ι Q a -
       s • CliffordAlgebra.ι Q b) * CliffordAlgebra.ι Q a := by
        rw [map_sub, map_smul, map_smul]
    _ = c • (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q a) -
        s • (CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q a) := by
        simp only [sub_mul, smul_mul_assoc]
    _ = c • (1 : C) +
        s • (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) := by
          rw [haa, hba]
          simp only [smul_neg, sub_neg_eq_add]

/-- The actual original positive-i Y source bivector has the
same genuine two-source-generator factorization, with axes (2,0). -/
theorem sourceYPlane_twoVector_factor
    (α : RealSpinBlock) (c s : ℝ) :
    CliffordAlgebra.ι Q
      (c • sourceBlockColorAxis α 2 -
       s • sourceBlockColorAxis α 0) *
      CliffordAlgebra.ι Q (sourceBlockColorAxis α 2) =
      c • (1 : C) + s • sourceYBivector α := by
  change
    CliffordAlgebra.ι Q
      (c • sourceBlockColorAxis α 2 - s • sourceBlockColorAxis α 0) *
      CliffordAlgebra.ι Q (sourceBlockColorAxis α 2) =
      c • (1 : C) +
        s • (CliffordAlgebra.ι Q (sourceBlockColorAxis α 2) *
             CliffordAlgebra.ι Q (sourceBlockColorAxis α 0))
  exact sourceColorPlane_twoVector_factor α 2 0 (by decide) c s

#print axioms sourceColorPlane_firstVector_unit
#print axioms sourceColorPlane_twoVector_factor
#print axioms sourceYPlane_twoVector_factor
end
end FCP.BFSSS1V52L4
