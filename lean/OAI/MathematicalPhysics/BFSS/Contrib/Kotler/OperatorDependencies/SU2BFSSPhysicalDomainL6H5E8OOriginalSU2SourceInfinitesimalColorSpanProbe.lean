import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8NOriginalColorTopologicalClosureProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6VOriginalPlusIConjugationDerivativeProbe
import OAI.MathematicalPhysics.BFSS.ColorMatrices

/-!
L6H5E8O — source-exact Lie-algebra COLOR TANGENT SPAN,
a finite-dimensional prerequisite for the remaining
SU2 subgroup-density problem (GitHub issue #27).

Any traceless skew-Hermitian 2-by-2 complex matrix W
is a REAL linear combination of the EXACT original
source infinitesimal color directions +i*T_c.
This follows by transporting the ALREADY QUALIFIED
original color_spanning field from traceless Hermitian
to traceless skew-Hermitian matrices via multiplication
by -i; no fabricated Lie basis or substitution.

This theorem does NOT by itself imply that the generated
one-parameter SU2 subgroup is dense or all of SU2.
A separate local-surjectivity and global-connectedness
(or constructive Euler) argument remains necessary.
The precise original +i source curve and Fock action
are not modified. Strict theorem/axiom audit required.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8O
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
-- #335: pairedAlgebraData is the qualified G1A source witness.
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4J
open Matrix

/-- Multiplication by original -i converts a skew-Hermitian
color-matrix tangent into a Hermitian source color matrix.
The inverse transport is exactly multiplication by +i. -/
theorem source_skewHermitian_to_hermitian
    (W : ColorMatrix 2)
    (hskew : Wᴴ = -W) :
    (((-Complex.I : ℂ) • W) : ColorMatrix 2).IsHermitian := by
  change ((-Complex.I : ℂ) • W)ᴴ = (-Complex.I : ℂ) • W
  -- #335: `Complex.conj_neg` does not exist in pinned Mathlib.
  -- Isolate the scalar star identity rather than rewriting the
  -- concrete color matrix or relying on an unqualified simp lemma.
  have hstar : star (-Complex.I : ℂ) = (Complex.I : ℂ) := by simp
  rw [Matrix.conjTranspose_smul, hskew, hstar,
    smul_neg, neg_smul]

/-- The previous transport preserves source tracelessness;
this is a separate named interface to the exact
AlgebraData.color_spanning theorem. -/
theorem source_skewHermitian_to_traceless
    (W : ColorMatrix 2)
    (htrace : Matrix.trace W = 0) :
    Matrix.trace (((-Complex.I : ℂ) • W) : ColorMatrix 2) = 0 := by
  rw [Matrix.trace_smul, htrace, smul_zero]

/-- Exact BFSS color Lie tangent spanning statement.
NO SU2 matrix exponentiation, Lie-group surjectivity,
or whole-group generation is assumed in this theorem. -/
theorem source_original_color_tangent_real_spanning
    (W : ColorMatrix 2)
    (hskew : Wᴴ = -W)
    (htrace : Matrix.trace W = 0) :
    ∃ a : ColorIndex 2 → ℝ,
      W = ∑ c : ColorIndex 2,
        (a c : ℂ) •
          ((Complex.I : ℂ) • pairedAlgebraData.color c) := by
  let H : ColorMatrix 2 := (-Complex.I : ℂ) • W
  have hH : H.IsHermitian :=
    source_skewHermitian_to_hermitian W hskew
  have ht : Matrix.trace H = 0 :=
    source_skewHermitian_to_traceless W htrace
  obtain ⟨a, ha⟩ := pairedAlgebraData.color_spanning H hH ht
  refine ⟨a, ?_⟩
  have hback : W = (Complex.I : ℂ) • H := by
    dsimp [H]
    rw [smul_smul]
    have hi : (Complex.I : ℂ) * (-Complex.I) = 1 := by
      rw [mul_neg, Complex.I_mul_I]
      ring
    rw [hi, one_smul]
  calc
    W = (Complex.I : ℂ) • H := hback
    _ = (Complex.I : ℂ) •
        (∑ c : ColorIndex 2, (a c : ℂ) • pairedAlgebraData.color c) :=
      congrArg (fun X : ColorMatrix 2 => (Complex.I : ℂ) • X) ha
    _ = ∑ c : ColorIndex 2,
        (a c : ℂ) • ((Complex.I : ℂ) • pairedAlgebraData.color c) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [smul_smul, smul_smul]
      congr 1
      ring

#print axioms source_skewHermitian_to_hermitian
#print axioms source_skewHermitian_to_traceless
#print axioms source_original_color_tangent_real_spanning
#check @source_original_color_tangent_real_spanning

end
end FCP.BFSSSU2PhysicalDomainL6H5E8O
