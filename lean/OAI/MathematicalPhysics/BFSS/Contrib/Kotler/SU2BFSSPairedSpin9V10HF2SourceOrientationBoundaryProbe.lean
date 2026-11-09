import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HTypedDeterminantFixture

/-!
K1D18V10H-F2 — isolate the precise original paired Fock
orientation equivalence after qualified V10H-F1.

All proofs import ONLY ACCEPTED V10G and the new F1 fixture.
The unqualified V10H determinant-character source is NOT
imported. In particular, no recursive character expansion.

A source group Spin9 → O(original 48) is already accepted.
The results below prove determinant-sign equality and the
exact membership iff between SO(original 48) and SO16.
These do NOT assert that any image is orientation preserving.

F2 CANDIDATE until exact strict source/type/axiom CI passes.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- The original paired 48 determinant squares to one,
by the accepted source-gamma O16 determinant equality. -/
theorem pairedDetSquareOne (g : spinGroup source9Quadratic) :
    ((((source9SpinOriginalPaired48OrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ)).det) ^ 2 = 1 := by
  rw [pairedDetEqualGamma g]
  exact gammaDetSquareOne g

/-- An ACTUAL original G1A paired-Fock O48 Spin9 image lies
in SO48 if and only if its original gamma16 image has
determinant +1. No orientation hypothesis is invented. -/
theorem pairedSO_iff_gammaDetOne
    (g : spinGroup source9Quadratic) :
    ((source9SpinOriginalPaired48OrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ) ∈
      Matrix.specialOrthogonalGroup Source48Label ℝ ↔
      (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) = 1 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · intro h
    exact (pairedDetEqualGamma g).symm.trans h.2
  · intro h
    exact ⟨(source9SpinOriginalPaired48OrthogonalHom g).property,
      (pairedDetEqualGamma g).trans h⟩

/-- Equivalent source-exact SO membership on original
paired 48 and gamma16. Since the target uses the actual
Spin9 source elements, this is not a result about arbitrary
unrelated O16/O48 matrices. -/
theorem pairedSO_iff_gammaSO
    (g : spinGroup source9Quadratic) :
    ((source9SpinOriginalPaired48OrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ) ∈
      Matrix.specialOrthogonalGroup Source48Label ℝ ↔
    ((source9SpinGammaOrthogonalHom g) : GammaMatrix) ∈
      Matrix.specialOrthogonalGroup SpinIndex ℝ := by
  rw [pairedSO_iff_gammaDetOne g, Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · intro h
    exact ⟨(source9SpinGammaOrthogonalHom g).property, h⟩
  · intro h
    exact h.2

#print axioms pairedDetSquareOne
#print axioms pairedSO_iff_gammaDetOne
#print axioms pairedSO_iff_gammaSO

end
end FCP.BFSSPairedSpin9DetFixture
