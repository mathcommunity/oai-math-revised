import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CRExteriorContractionTransport
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10ZSourceNineExteriorPBWOrderedWordProbe

/-! F10CS: contraction columns for the existing original-nine exterior PBW basis.
Reuse F10Z's basis and ordered words with their native Fin 9 order. Contract an absent
coordinate to zero and a least present coordinate with coefficient +1. Reconstruct the
empty coefficient only under an explicit vanishing condition on every nonempty index.
The common-contraction-kernel scalar theorem and source Spin equality remain open.
Candidate until complete strict source compilation and independent audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum

theorem source9ExteriorCoordinateWord_cons (j : SpaceIndex) (xs : List SpaceIndex) :
    source9ExteriorCoordinateWord (j :: xs) =
      ExteriorAlgebra.ι ℝ (Pi.single j (1 : ℝ) : SpaceIndex → ℝ) *
        source9ExteriorCoordinateWord xs := by
  simp [source9ExteriorCoordinateWord]

theorem source9ExteriorCoordinateWord_contraction_zero_of_not_mem
    (j : SpaceIndex) (xs : List SpaceIndex) (hj : j ∉ xs) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (SpaceIndex → ℝ)))
      (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ))
      (source9ExteriorCoordinateWord xs) = 0 := by
  induction xs with
  | nil => simp [source9ExteriorCoordinateWord, CliffordAlgebra.contractLeft_one]
  | cons k ks ih =>
      have hjk : j ≠ k := by
        intro h
        exact hj (by simp [h])
      have hks : j ∉ ks := by
        intro h
        exact hj (by simp [h])
      rw [source9ExteriorCoordinateWord_cons, CliffordAlgebra.contractLeft_ι_mul]
      have hcoord : (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ))
          (Pi.single k (1 : ℝ) : SpaceIndex → ℝ) = 0 := by
        simp [hjk]
      rw [hcoord, ih hks]
      simp

theorem source9ExteriorCoordinateWord_leading_contraction
    (j : SpaceIndex) (xs : List SpaceIndex) (hj : j ∉ xs) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (SpaceIndex → ℝ)))
      (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ))
      (source9ExteriorCoordinateWord (j :: xs)) = source9ExteriorCoordinateWord xs := by
  rw [source9ExteriorCoordinateWord_cons, CliffordAlgebra.contractLeft_ι_mul]
  have hcoord : (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ))
      (Pi.single j (1 : ℝ) : SpaceIndex → ℝ) = 1 := by simp
  rw [hcoord, source9ExteriorCoordinateWord_contraction_zero_of_not_mem j xs hj]
  simp

theorem source9ExteriorPBWOrderedLabels_mem_finset
    (I : Finset SpaceIndex) (j : SpaceIndex) (hj : j ∈ source9ExteriorPBWOrderedLabels I) :
    j ∈ I := by
  classical
  change j ∈ List.ofFn (fun i : Fin I.card => I.orderEmbOfFin rfl i) at hj
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hj
  rw [← hi]
  exact Finset.orderEmbOfFin_mem I rfl i

theorem source9ExteriorPBWBasis_coordinateContraction_zero_of_not_mem
    (I : Finset SpaceIndex) (j : SpaceIndex) (hj : j ∉ I) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (SpaceIndex → ℝ)))
      (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ)) (source9ExteriorPBWBasis I) = 0 := by
  rw [source9ExteriorPBWBasis_eq_coordinateWord]
  apply source9ExteriorCoordinateWord_contraction_zero_of_not_mem
  intro h
  exact hj (source9ExteriorPBWOrderedLabels_mem_finset I j h)

private theorem source9ExteriorPBWOrderedLabels_eq_sort (I : Finset SpaceIndex) :
    source9ExteriorPBWOrderedLabels I = I.sort := by
  classical
  change (List.ofFn (fun i : Fin I.card => I.orderEmbOfFin rfl i)) = I.sort
  rw [List.ofFn_eq_map]
  exact Finset.listMap_orderEmbOfFin_finRange I rfl

theorem source9ExteriorPBWOrderedLabels_cons_of_least
    (I : Finset SpaceIndex) (j : SpaceIndex) (hj : j ∈ I) (hmin : ∀ k ∈ I, j ≤ k) :
    source9ExteriorPBWOrderedLabels I =
      j :: source9ExteriorPBWOrderedLabels (I.erase j) := by
  classical
  rw [source9ExteriorPBWOrderedLabels_eq_sort, source9ExteriorPBWOrderedLabels_eq_sort]
  have hmin' : ∀ k ∈ I.erase j, j ≤ k := by
    intro k hk
    exact hmin k (Finset.mem_of_mem_erase hk)
  calc
    I.sort = (insert j (I.erase j)).sort := by rw [Finset.insert_erase hj]
    _ = j :: (I.erase j).sort := Finset.sort_insert (r := LE.le) hmin' (by simp)

theorem source9ExteriorPBWBasis_contraction_erase_of_least
    (I : Finset SpaceIndex) (j : SpaceIndex) (hj : j ∈ I) (hmin : ∀ k ∈ I, j ≤ k) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (SpaceIndex → ℝ)))
      (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ)) (source9ExteriorPBWBasis I) =
        source9ExteriorPBWBasis (I.erase j) := by
  classical
  have htail : j ∉ source9ExteriorPBWOrderedLabels (I.erase j) := by
    intro h
    have he : j ∈ I.erase j := source9ExteriorPBWOrderedLabels_mem_finset (I.erase j) j h
    simp at he
  rw [source9ExteriorPBWBasis_eq_coordinateWord,
    source9ExteriorPBWOrderedLabels_cons_of_least I j hj hmin,
    source9ExteriorCoordinateWord_leading_contraction j _ htail]
  exact (source9ExteriorPBWBasis_eq_coordinateWord (I.erase j)).symm

theorem source9ExteriorPBWBasis_empty_eq_one :
    source9ExteriorPBWBasis (∅ : Finset SpaceIndex) =
      (1 : ExteriorAlgebra ℝ (SpaceIndex → ℝ)) := by
  classical
  change (Pi.basisFun ℝ SpaceIndex).ExteriorAlgebra (∅ : Finset SpaceIndex) = _
  simp only [ExteriorAlgebra.basis_apply, Finset.card_empty, ExteriorAlgebra.ιMulti_family]
  exact ExteriorAlgebra.ιMulti_zero_apply (R := ℝ) _

/-- Scalar reconstruction requires the explicit vanishing of every nonempty PBW coefficient. -/
theorem source9Exterior_eq_scalar_of_nonempty_coefficients_zero
    (x : ExteriorAlgebra ℝ (SpaceIndex → ℝ))
    (hz : ∀ I : Finset SpaceIndex, I ≠ ∅ → source9ExteriorPBWBasis.repr x I = 0) :
    x = algebraMap ℝ (ExteriorAlgebra ℝ (SpaceIndex → ℝ))
      (source9ExteriorPBWBasis.repr x ∅) := by
  classical
  have hf : source9ExteriorPBWBasis.repr x =
      Finsupp.single (∅ : Finset SpaceIndex) (source9ExteriorPBWBasis.repr x ∅) := by
    ext I
    by_cases hI : I = ∅
    · subst I
      simp
    · simp [hI, hz I hI]
  calc
    x = source9ExteriorPBWBasis.repr.symm (source9ExteriorPBWBasis.repr x) :=
      (source9ExteriorPBWBasis.repr.symm_apply_apply x).symm
    _ = source9ExteriorPBWBasis.repr.symm
        (Finsupp.single ∅ (source9ExteriorPBWBasis.repr x ∅)) :=
      congrArg source9ExteriorPBWBasis.repr.symm hf
    _ = (source9ExteriorPBWBasis.repr x ∅) • source9ExteriorPBWBasis (∅ : Finset SpaceIndex) :=
      source9ExteriorPBWBasis.repr_symm_single ∅ (source9ExteriorPBWBasis.repr x ∅)
    _ = algebraMap ℝ (ExteriorAlgebra ℝ (SpaceIndex → ℝ))
        (source9ExteriorPBWBasis.repr x ∅) := by
      rw [source9ExteriorPBWBasis_empty_eq_one]
      simp [Algebra.smul_def]

#print axioms source9ExteriorCoordinateWord_cons
#print axioms source9ExteriorCoordinateWord_contraction_zero_of_not_mem
#print axioms source9ExteriorCoordinateWord_leading_contraction
#print axioms source9ExteriorPBWOrderedLabels_mem_finset
#print axioms source9ExteriorPBWBasis_coordinateContraction_zero_of_not_mem
#print axioms source9ExteriorPBWOrderedLabels_cons_of_least
#print axioms source9ExteriorPBWBasis_contraction_erase_of_least
#print axioms source9ExteriorPBWBasis_empty_eq_one
#print axioms source9Exterior_eq_scalar_of_nonempty_coefficients_zero
end
end FCP.BFSSPairedSpin9Clifford
