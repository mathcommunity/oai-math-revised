import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D2E1OriginalPBWBasisAbsentCoordinateContractionProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D2E3OriginalPBWLeastCoordinateContractionProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D2E4OriginalPBWFinitelyOccupiedMinimumProbe

/-! Owner FCP source-only port, original cc608e2282e1b32bb11bbb64424e4775b28138e2; Git blob 1c7b4543ca810a4017767ee79d1a0a5942c130cd.
Imports alone have been restructured; theorem statements/proof bodies unchanged.
The omitted original Spin ancestry is not claimed qualified by this port.
Status: provisional pending fresh owner strict-gate acceptance. -/

/-!
K1D2F1: coefficient separation for the ACTUAL original F20B PBW exterior basis.

For a coordinate j no greater than all labels in every nonzero
supported original PBW basis index, contraction recovers the coefficient
of any supported index I containing j at I.erase j.  No cancellation is
possible, by accepted source-exact erasure injectivity.  No statement about
Spin(48) kernel or physical BFSS spectral existence is asserted.

Candidate mathematical statement: STRICT GATE REQUIRED; not accepted on commit.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52K1D2F1
noncomputable section
open FCP.BFSSS1V0

private abbrev E := ExteriorAlgebra ℝ Source48Vector
private abbrev Q0 : QuadraticForm ℝ Source48Vector := 0
private abbrev B : Module.Basis (Finset Source48Label) ℝ E :=
  FCP.BFSSS1V52K1D2C.originalSourceExteriorPBWBasis

local instance : LinearOrder Source48Label := by
  classical
  exact linearOrderOfSTO WellOrderingRel
local instance : LE Source48Label :=
  (instDistribLatticeOfLinearOrder (α := Source48Label)).toSemilatticeInf.toLE

/-- A genuine original F20B exterior PBW coefficient cannot cancel
under contraction at the globally least supported source coordinate. -/
theorem originalSourcePBWLeastContraction_coefficient
    (x : E) (j : Source48Label)
    (hmin : ∀ (J : Finset Source48Label),
      J ∈ (B.repr x).support →
      ∀ (k : Source48Label), k ∈ J → j ≤ k)
    (I : Finset Source48Label)
    (hI : I ∈ (B.repr x).support) (hj : j ∈ I) :
    B.repr
      (CliffordAlgebra.contractLeft (Q := Q0)
        (LinearMap.proj j : Module.Dual ℝ Source48Vector) x)
      (I.erase j) = B.repr x I := by
  classical
  let c := B.repr x
  let d := CliffordAlgebra.contractLeft (Q := Q0)
    (LinearMap.proj j : Module.Dual ℝ Source48Vector)
  have hsum : (c.sum fun J a => a • B J) = x := by
    simpa only [c, Finsupp.linearCombination_apply] using
      (B.linearCombination_repr x)
  have hterm (J : Finset Source48Label) (hJ : J ∈ c.support) :
      B.repr (d (c J • B J)) (I.erase j) =
        if J = I then c I else 0 := by
    by_cases hjJ : j ∈ J
    · have hleast : ∀ k ∈ J, j ≤ k := hmin J hJ
      change B.repr
        (CliffordAlgebra.contractLeft (Q := Q0)
          (LinearMap.proj j : Module.Dual ℝ Source48Vector)
          (c J • B J)) (I.erase j) =
          if J = I then c I else 0
      rw [map_smul,
        FCP.BFSSS1V52K1D2E3.originalSourceExteriorPBWBasis_contraction_erase_of_least
          J j hjJ hleast, map_smul]
      by_cases hJI : J = I
      · subst J
        simp
      · have herase : J.erase j ≠ I.erase j := by
          intro he
          exact hJI
            (FCP.BFSSS1V52K1D2D.originalSourceFinset_erase_injective_at_present_label
              j J I hjJ hj he)
        simp [hJI, herase]
    · have hJI : J ≠ I := by
        intro he
        subst J
        exact hjJ hj
      change B.repr
        (CliffordAlgebra.contractLeft (Q := Q0)
          (LinearMap.proj j : Module.Dual ℝ Source48Vector)
          (c J • B J)) (I.erase j) =
          if J = I then c I else 0
      rw [map_smul,
        FCP.BFSSS1V52K1D2E1.originalSourceExteriorPBWBasis_coordinateContraction_zero_of_not_mem
          J j hjJ]
      simp [hJI]
  calc
    B.repr (d x) (I.erase j) =
        B.repr (d (c.sum fun J a => a • B J)) (I.erase j) := by rw [hsum]
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

#print axioms originalSourcePBWLeastContraction_coefficient

end
end FCP.BFSSS1V52K1D2F1
