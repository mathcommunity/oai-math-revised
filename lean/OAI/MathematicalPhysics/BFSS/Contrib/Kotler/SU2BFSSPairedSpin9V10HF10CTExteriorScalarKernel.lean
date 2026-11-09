import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CSExteriorPBWContractions
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Max

/-! F10CT: native-nine finite PBW coefficient isolation and the exterior scalar kernel.
Use the actual finitely supported expansion and its least occupied coordinate. No signed
full-basis enumeration or replacement order is introduced. Compose with accepted scalar
transport for the actual natural-action kernel and reconstruction-relative element.
Two-sign classification, local source equality and coverage remain separate obligations.
Candidate until complete strict source compilation and independent audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open scoped BigOperators

private abbrev E := ExteriorAlgebra ℝ (SpaceIndex → ℝ)
private abbrev Q0 : QuadraticForm ℝ (SpaceIndex → ℝ) := 0
private abbrev B : Module.Basis (Finset SpaceIndex) ℝ E := source9ExteriorPBWBasis

/-- Exactly the original labels occurring in the nonzero finite PBW coefficient support. -/
noncomputable def source9ExteriorPBWOccupiedLabels (x : E) : Finset SpaceIndex := by
  classical
  exact (B.repr x).support.biUnion (fun I : Finset SpaceIndex => I)

private theorem supported_member_occupied (x : E) (I : Finset SpaceIndex)
    (hI : I ∈ (B.repr x).support) (j : SpaceIndex) (hj : j ∈ I) :
    j ∈ source9ExteriorPBWOccupiedLabels x := by
  classical
  simp only [source9ExteriorPBWOccupiedLabels, Finset.mem_biUnion]
  exact ⟨I, hI, hj⟩

private theorem erase_injective_at_present (j : SpaceIndex) (I J : Finset SpaceIndex)
    (hI : j ∈ I) (hJ : j ∈ J) (he : I.erase j = J.erase j) : I = J := by
  calc
    I = insert j (I.erase j) := (Finset.insert_erase hI).symm
    _ = insert j (J.erase j) := congrArg (fun K : Finset SpaceIndex => insert j K) he
    _ = J := Finset.insert_erase hJ

/-- At a globally least supported coordinate, erasure isolates the actual PBW coefficient. -/
theorem source9ExteriorPBWLeastContraction_coefficient
    (x : E) (j : SpaceIndex)
    (hmin : ∀ J : Finset SpaceIndex, J ∈ (B.repr x).support → ∀ k ∈ J, j ≤ k)
    (I : Finset SpaceIndex) (hI : I ∈ (B.repr x).support) (hj : j ∈ I) :
    B.repr (CliffordAlgebra.contractLeft (Q := Q0)
      (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ)) x) (I.erase j) = B.repr x I := by
  classical
  let c := B.repr x
  let d := CliffordAlgebra.contractLeft (Q := Q0)
    (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ))
  have hsum : (c.sum fun J a => a • B J) = x := by
    simpa only [c, Finsupp.linearCombination_apply] using (B.linearCombination_repr x)
  have hterm (J : Finset SpaceIndex) (hJ : J ∈ c.support) :
      B.repr (d (c J • B J)) (I.erase j) = if J = I then c I else 0 := by
    by_cases hjJ : j ∈ J
    · have hleast : ∀ k ∈ J, j ≤ k := hmin J hJ
      change B.repr (CliffordAlgebra.contractLeft (Q := Q0)
        (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ)) (c J • B J)) (I.erase j) =
          if J = I then c I else 0
      rw [map_smul, source9ExteriorPBWBasis_contraction_erase_of_least J j hjJ hleast, map_smul]
      by_cases hJI : J = I
      · subst J
        simp
      · have herase : J.erase j ≠ I.erase j := by
          intro he
          exact hJI (erase_injective_at_present j J I hjJ hj he)
        simp [hJI, herase]
    · have hJI : J ≠ I := by
        intro he
        subst J
        exact hjJ hj
      change B.repr (CliffordAlgebra.contractLeft (Q := Q0)
        (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ)) (c J • B J)) (I.erase j) =
          if J = I then c I else 0
      rw [map_smul, source9ExteriorPBWBasis_coordinateContraction_zero_of_not_mem J j hjJ]
      simp [hJI]
  calc
    B.repr (d x) (I.erase j) = B.repr (d (c.sum fun J a => a • B J)) (I.erase j) := by rw [hsum]
    _ = ∑ J ∈ c.support, B.repr (d (c J • B J)) (I.erase j) := by
      simp only [Finsupp.sum, map_sum]
      rw [Finset.sum_apply']
    _ = ∑ J ∈ c.support, (if J = I then c I else 0) := by
      apply Finset.sum_congr rfl
      intro J hJ
      exact hterm J hJ
    _ = c I := by
      rw [Finset.sum_eq_single I]
      · simp
      · intro J hJ hJI
        simp [hJI]
      · intro hnot
        exact (hnot hI).elim

theorem source9Exterior_commonContractions_nonemptyCoefficients_zero
    (x : E)
    (hzero : ∀ j : SpaceIndex, CliffordAlgebra.contractLeft (Q := Q0)
      (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ)) x = 0) :
    ∀ I : Finset SpaceIndex, I ≠ ∅ → B.repr x I = 0 := by
  classical
  let occ := source9ExteriorPBWOccupiedLabels x
  have hempty : occ = ∅ := by
    by_contra hnot
    have hocc : occ.Nonempty := Finset.nonempty_iff_ne_empty.mpr hnot
    let j : SpaceIndex := occ.min' hocc
    have hjocc : j ∈ occ := Finset.min'_mem occ hocc
    have hsome : ∃ I ∈ (B.repr x).support, j ∈ I := by
      simpa only [occ, source9ExteriorPBWOccupiedLabels, Finset.mem_biUnion] using hjocc
    obtain ⟨I, hI, hjI⟩ := hsome
    have hleast : ∀ J : Finset SpaceIndex, J ∈ (B.repr x).support → ∀ k ∈ J, j ≤ k := by
      intro J hJ k hk
      exact Finset.min'_le _ k (supported_member_occupied x J hJ k hk)
    have hcoeff := source9ExteriorPBWLeastContraction_coefficient x j hleast I hI hjI
    have hczero : B.repr x I = 0 := by
      rw [hzero j] at hcoeff
      simpa using hcoeff.symm
    exact (Finsupp.mem_support_iff.mp hI) hczero
  intro I hI
  by_contra hn
  have hs : I ∈ (B.repr x).support := Finsupp.mem_support_iff.mpr hn
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hI
  have ho := supported_member_occupied x I hs j hj
  change j ∈ occ at ho
  rw [hempty] at ho
  simp at ho

theorem source9Exterior_commonCoordinateKernel_eq_scalar
    (x : E)
    (hzero : ∀ j : SpaceIndex, CliffordAlgebra.contractLeft (Q := Q0)
      (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ)) x = 0) :
    x = algebraMap ℝ E (B.repr x ∅) :=
  source9Exterior_eq_scalar_of_nonempty_coefficients_zero x
    (source9Exterior_commonContractions_nonemptyCoefficients_zero x hzero)

theorem source9Exterior_commonCoordinateKernel_iff_scalar (x : E) :
    (∀ j : SpaceIndex, CliffordAlgebra.contractLeft (Q := Q0)
      (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ)) x = 0) ↔
      ∃ c : ℝ, x = algebraMap ℝ E c := by
  constructor
  · intro hz
    exact ⟨B.repr x ∅, source9Exterior_commonCoordinateKernel_eq_scalar x hz⟩
  · rintro ⟨c, rfl⟩
    intro j
    exact CliffordAlgebra.contractLeft_algebraMap (Q := Q0)
      (d := (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ))) c

theorem source9NaturalKernel_clifford_eq_scalar
    (g : spinGroup source9Quadratic)
    (hg : ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) = 1) :
    (g : CliffordAlgebra source9Quadratic) =
      algebraMap ℝ (CliffordAlgebra source9Quadratic)
        (B.repr ((CliffordAlgebra.equivExterior source9Quadratic)
          (g : CliffordAlgebra source9Quadratic)) ∅) :=
  (source9Clifford_exterior_eq_scalar_iff _ _).1
    (source9Exterior_commonCoordinateKernel_eq_scalar _
      (source9NaturalKernel_exteriorCoordinateContractions_zero g hg))

theorem source9NaturalMatrix_eq_one_iff_clifford_scalar (g : spinGroup source9Quadratic) :
    ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) = 1 ↔
      ∃ c : ℝ, (g : CliffordAlgebra source9Quadratic) =
        algebraMap ℝ (CliffordAlgebra source9Quadratic) c := by
  constructor
  · intro hk
    exact ⟨B.repr ((CliffordAlgebra.equivExterior source9Quadratic)
      (g : CliffordAlgebra source9Quadratic)) ∅, source9NaturalKernel_clifford_eq_scalar g hk⟩
  · rintro ⟨c, hc⟩
    apply (source9NaturalMatrix_eq_one_iff_generator_commutes g).2
    intro v
    rw [hc]
    exact Algebra.commutes c (CliffordAlgebra.ι source9Quadratic v)

theorem source9NaturalMatrix_eq_iff_relative_clifford_scalar (g h : spinGroup source9Quadratic) :
    ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) =
      ((source9SpinVectorOrthogonalHom h) : Matrix SpaceIndex SpaceIndex ℝ) ↔
      ∃ c : ℝ, ((g * h⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic) =
        algebraMap ℝ (CliffordAlgebra source9Quadratic) c :=
  (source9NaturalMatrix_eq_iff_relative_kernel g h).trans
    (source9NaturalMatrix_eq_one_iff_clifford_scalar (g * h⁻¹))

theorem source9Reconstruction_relative_clifford_eq_scalar_on_sourceNeighborhood
    (g : spinGroup source9Quadratic) (hg : g ∈ source9SpinNaturalMatrixRecoveryNeighborhood) :
    ((source9SpinCoordinateReconstruction g * g⁻¹ : spinGroup source9Quadratic) :
      CliffordAlgebra source9Quadratic) =
      algebraMap ℝ (CliffordAlgebra source9Quadratic)
        (B.repr ((CliffordAlgebra.equivExterior source9Quadratic)
          ((source9SpinCoordinateReconstruction g * g⁻¹ : spinGroup source9Quadratic) :
            CliffordAlgebra source9Quadratic)) ∅) :=
  source9NaturalKernel_clifford_eq_scalar (source9SpinCoordinateReconstruction g * g⁻¹)
    (source9Reconstruction_relative_kernel_on_sourceNeighborhood g hg)

#print axioms source9ExteriorPBWOccupiedLabels
#print axioms source9ExteriorPBWLeastContraction_coefficient
#print axioms source9Exterior_commonContractions_nonemptyCoefficients_zero
#print axioms source9Exterior_commonCoordinateKernel_eq_scalar
#print axioms source9Exterior_commonCoordinateKernel_iff_scalar
#print axioms source9NaturalKernel_clifford_eq_scalar
#print axioms source9NaturalMatrix_eq_one_iff_clifford_scalar
#print axioms source9NaturalMatrix_eq_iff_relative_clifford_scalar
#print axioms source9Reconstruction_relative_clifford_eq_scalar_on_sourceNeighborhood
end
end FCP.BFSSPairedSpin9Clifford
