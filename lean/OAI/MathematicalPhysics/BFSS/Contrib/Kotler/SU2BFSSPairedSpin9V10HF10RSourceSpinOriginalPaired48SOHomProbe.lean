import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10QSourceSpinOrientationDetOneProbe

/-!
K1D18V10H-F10R — EXACT algebraic source Spin9 action valued in
the original G1A Fock-paired 48-label special orthogonal group.

The accepted V10G conditional source SO(48) membership bridge
takes the original real gamma Spin9 determinant-one hypothesis.
F10Q strictly qualified that exact hypothesis on every genuine
Mathlib source spinGroup element.

This micro-gate discharges V10G's hypothesis without changing
the accepted V10F global original-label O(48) representation,
and constructs a genuine MonoidHom to the exact Matrix
specialOrthogonalGroup for the ORIGINAL paired source labels.
It independently checks the underlying-matrix identity.

ALGEBRAIC group map ONLY. No source Spin9 topology, Spin48 lift,
covering, Fock Hilbert-space implementation, gauge action or
physical BFSS spectral claim is asserted.

CANDIDATE until pinned strict Lean and three exact declaration
type/axiom checks pass.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9DetFixture
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- The ACTUAL original paired-Fock 48-label source Spin9 action
is in the genuine matrix specialOrthogonalGroup; use exactly
the accepted V10G conditional and F10Q determinant +1. -/
theorem source9SpinOriginalPaired48_mem_specialOrthogonal
    (g : spinGroup source9Quadratic) :
    ((source9SpinOriginalPaired48OrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ) ∈
      Matrix.specialOrthogonalGroup Source48Label ℝ := by
  apply source9SpinOriginalPaired48_mem_specialOrthogonal_of_gamma_det_one g
  rw [← gammaDetDirectHom_apply]
  exact gammaDetDirectHom_eq_one g

/-- Global ALgebraic Spin9 to SO(original paired-48) group map,
constructed from the accepted V10F exact original O(48)
homomorphism and the new source-exact membership proof. -/
noncomputable def source9SpinOriginalPaired48SpecialOrthogonalHom :
    spinGroup source9Quadratic →*
      Matrix.specialOrthogonalGroup Source48Label ℝ where
  toFun g :=
    ⟨((source9SpinOriginalPaired48OrthogonalHom g) :
        Matrix Source48Label Source48Label ℝ),
      source9SpinOriginalPaired48_mem_specialOrthogonal g⟩
  map_one' := by
    apply Subtype.ext
    change ((source9SpinOriginalPaired48OrthogonalHom
      (1 : spinGroup source9Quadratic)) :
        Matrix Source48Label Source48Label ℝ) = 1
    rw [map_one]
    rfl
  map_mul' := by
    intro g h
    apply Subtype.ext
    change ((source9SpinOriginalPaired48OrthogonalHom (g * h)) :
      Matrix Source48Label Source48Label ℝ) =
        ((source9SpinOriginalPaired48OrthogonalHom g) :
          Matrix Source48Label Source48Label ℝ) *
        ((source9SpinOriginalPaired48OrthogonalHom h) :
          Matrix Source48Label Source48Label ℝ)
    rw [map_mul]
    rfl

/-- The SO-valued homomorphism has EXACTLY the preexisting
original V10F paired-label O(48) underlying matrix,
not a replacement 48-dimensional representation. -/
theorem source9SpinOriginalPaired48SpecialOrthogonalHom_apply
    (g : spinGroup source9Quadratic) :
    ((source9SpinOriginalPaired48SpecialOrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ) =
    ((source9SpinOriginalPaired48OrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ) := rfl

#print axioms source9SpinOriginalPaired48_mem_specialOrthogonal
#print axioms source9SpinOriginalPaired48SpecialOrthogonalHom
#print axioms source9SpinOriginalPaired48SpecialOrthogonalHom_apply

end
end FCP.BFSSPairedSpin9Clifford
