import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BZFullNaturalMatrixWordDerivative
import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Pi

/-!
F10CA — nonredundant native strict-plane coordinates for canonical so(9,R).

Use precisely the original spatial pairs r < s. Reconstruct a skew matrix
from its upper entries, and exhibit an explicit real linear equivalence
with Mathlib's canonical orthogonal Lie algebra. The reconstruction is
also the literal sum of the native E_rs - E_sr planes, without a half factor.

This supplies an algebraic model, not a word order, subgroup chart,
tangent identification, local kernel theorem or manifold differential.
Candidate until strict source and independent type/axiom audits pass.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSPairedSpin9Plane
open scoped BigOperators

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Each original spatial plane occurs once, with its increasing orientation. -/
abbrev source9StrictPlaneIndex :=
  {p : SpaceIndex × SpaceIndex // p.1 < p.2}

/-- There are exactly 36 increasing pairs of the original nine labels. -/
theorem source9StrictPlaneIndex_card : Fintype.card source9StrictPlaneIndex = 36 := by
  decide

/-- Reconstruct the full matrix from upper entries, with negative lower entries. -/
noncomputable def source9StrictPlaneMatrix (c : source9StrictPlaneIndex → ℝ) :
    Matrix SpaceIndex SpaceIndex ℝ :=
  fun i j =>
    if h : i < j then c ⟨(i, j), h⟩
    else if h : j < i then -c ⟨(j, i), h⟩
    else 0

/-- The reconstruction is skew in the original matrix carrier. -/
theorem source9StrictPlaneMatrix_transpose (c : source9StrictPlaneIndex → ℝ) :
    (source9StrictPlaneMatrix c).transpose = -source9StrictPlaneMatrix c := by
  apply Matrix.ext
  intro i j
  change source9StrictPlaneMatrix c j i = -source9StrictPlaneMatrix c i j
  by_cases hij : i < j
  · have hji : ¬j < i := not_lt_of_gt hij
    simp [source9StrictPlaneMatrix, hij, hji]
  · by_cases hji : j < i
    · simp [source9StrictPlaneMatrix, hij, hji]
    · simp [source9StrictPlaneMatrix, hij, hji]

/-- Exact linear model of canonical Mathlib so(9,R), inverse given by upper entries. -/
noncomputable def source9StrictPlaneModelEquiv :
    (source9StrictPlaneIndex → ℝ) ≃ₗ[ℝ] LieAlgebra.Orthogonal.so SpaceIndex ℝ where
  toFun c := ⟨source9StrictPlaneMatrix c, by
    rw [LieAlgebra.Orthogonal.mem_so]
    exact source9StrictPlaneMatrix_transpose c⟩
  invFun A p := A.val p.val.1 p.val.2
  left_inv c := by
    funext p
    change source9StrictPlaneMatrix c p.val.1 p.val.2 = c p
    simp only [source9StrictPlaneMatrix, dite_eq_left p.property]
  right_inv A := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change source9StrictPlaneMatrix
      (fun p : source9StrictPlaneIndex => A.val p.val.1 p.val.2) i j = A.val i j
    have hA : A.val.transpose = -A.val := by
      have hA_mem := A.property
      rw [LieAlgebra.Orthogonal.mem_so] at hA_mem
      exact hA_mem
    by_cases hij : i < j
    · simp [source9StrictPlaneMatrix, hij]
    · by_cases hji : j < i
      · have hentry : A.val j i = -(A.val i j) :=
          congrArg (fun M : Matrix SpaceIndex SpaceIndex ℝ => M i j) hA
        simp [source9StrictPlaneMatrix, hij, hji, hentry]
      · have heq : i = j :=
          le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
        subst j
        have hdiag : A.val i i = -(A.val i i) :=
          congrArg (fun M : Matrix SpaceIndex SpaceIndex ℝ => M i i) hA
        have hz : A.val i i = 0 := by linarith
        simp [source9StrictPlaneMatrix, hz]
  map_add' c d := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change source9StrictPlaneMatrix (c + d) i j =
      source9StrictPlaneMatrix c i j + source9StrictPlaneMatrix d i j
    by_cases hij : i < j
    · simp [source9StrictPlaneMatrix, hij]
    · by_cases hji : j < i
      · simp only [source9StrictPlaneMatrix, dite_eq_right hij, dite_eq_left hji,
          Pi.add_apply]
        abel
      · simp [source9StrictPlaneMatrix, hij, hji]
  map_smul' a c := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change source9StrictPlaneMatrix (a • c) i j = a • source9StrictPlaneMatrix c i j
    by_cases hij : i < j <;> by_cases hji : j < i <;>
      simp [source9StrictPlaneMatrix, hij, hji]

/-- The inverse is literally extraction of original upper-triangular entries. -/
theorem source9StrictPlaneModelEquiv_symm_apply
    (A : LieAlgebra.Orthogonal.so SpaceIndex ℝ) (p : source9StrictPlaneIndex) :
    source9StrictPlaneModelEquiv.symm A p = A.val p.val.1 p.val.2 := rfl

/-- A unit coordinate gives the exact full native plane, in increasing orientation. -/
theorem source9StrictPlaneModelEquiv_plane (p : source9StrictPlaneIndex) :
    (source9StrictPlaneModelEquiv (Pi.single p (1 : ℝ)) :
      Matrix SpaceIndex SpaceIndex ℝ) = coordinatePlane9 p.val.1 p.val.2 := by
  classical
  have hplane : coordinatePlane9 p.val.1 p.val.2 ∈
      LieAlgebra.Orthogonal.so SpaceIndex ℝ := by
    rw [LieAlgebra.Orthogonal.mem_so]
    exact coordinatePlane9_transpose p.val.1 p.val.2
  have heq : source9StrictPlaneModelEquiv (Pi.single p (1 : ℝ)) =
      ⟨coordinatePlane9 p.val.1 p.val.2, hplane⟩ := by
    apply source9StrictPlaneModelEquiv.symm.injective
    rw [source9StrictPlaneModelEquiv.symm_apply_apply]
    funext q
    rw [source9StrictPlaneModelEquiv_symm_apply]
    by_cases hpq : p = q
    · subst q
      simp [coordinatePlane9, p.property.ne, p.property.ne.symm]
    · have hcoords : ¬(q.val.1 = p.val.1 ∧ q.val.2 = p.val.2) := by
        intro h
        exact hpq (Subtype.ext (Prod.ext h.1.symm h.2.symm))
      have hswap : ¬(q.val.1 = p.val.2 ∧ q.val.2 = p.val.1) := by
        intro h
        have hq := q.property
        rw [h.1, h.2] at hq
        exact (not_lt_of_gt p.property) hq
      simp [coordinatePlane9, Ne.symm hpq, hcoords, hswap]
  exact congrArg (fun A : LieAlgebra.Orthogonal.so SpaceIndex ℝ => A.val) heq

/-- Reconstruction equals the literal nonredundant native-plane sum, with no half factor. -/
theorem source9StrictPlaneModelEquiv_apply_sum (c : source9StrictPlaneIndex → ℝ) :
    (source9StrictPlaneModelEquiv c : Matrix SpaceIndex SpaceIndex ℝ) =
      ∑ p : source9StrictPlaneIndex, c p • coordinatePlane9 p.val.1 p.val.2 := by
  classical
  let L : (source9StrictPlaneIndex → ℝ) →ₗ[ℝ] Matrix SpaceIndex SpaceIndex ℝ :=
    (LieAlgebra.Orthogonal.so SpaceIndex ℝ).toSubmodule.subtype.comp
      source9StrictPlaneModelEquiv.toLinearMap
  have hL (x : source9StrictPlaneIndex → ℝ) :
      L x = (source9StrictPlaneModelEquiv x : Matrix SpaceIndex SpaceIndex ℝ) := rfl
  have hsum := congrArg L (pi_eq_sum_univ' c)
  simp only [map_sum, map_smul] at hsum
  simpa only [hL, source9StrictPlaneModelEquiv_plane] using hsum

#print axioms source9StrictPlaneIndex_card
#print axioms source9StrictPlaneMatrix
#print axioms source9StrictPlaneMatrix_transpose
#print axioms source9StrictPlaneModelEquiv
#print axioms source9StrictPlaneModelEquiv_symm_apply
#print axioms source9StrictPlaneModelEquiv_plane
#print axioms source9StrictPlaneModelEquiv_apply_sum

end
end FCP.BFSSPairedSpin9Clifford
