import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D2F1OriginalPBWLeastContractionCoefficientProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D2E4OriginalPBWFinitelyOccupiedMinimumProbe

/-! Owner FCP source-only port, original cc608e2282e1b32bb11bbb64424e4775b28138e2; Git blob 0dc59f0b2b5fe38f761bac4277049498a67d2871.
Imports alone have been restructured; theorem statements/proof bodies unchanged.
The omitted original Spin ancestry is not claimed qualified by this port.
Status: provisional pending fresh owner strict-gate acceptance. -/

/-!
K1D2F2 — source-exact finite PBW occupancy vanishing from all original
48-coordinate exterior contractions. Depends on K1D2F1 coefficient
isolation, which MUST qualify through its own strict accepted-axiom gate
before this theorem is eligible for acceptance.

No substituted basis ordering, no total 2^48 expansion, no claim yet
that the original Clifford Spin(48) kernel or BFSS spectrum is proved.
STAGED, 0 ACCEPTED NEW ROOTS until independently strictly qualified.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52K1D2F2
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

/-- When every original coordinate contraction of a genuine exterior
element vanishes, there is no coordinate contained in any supported
nonzero finite PBW index. The scalar identification is a SEPARATE step. -/
theorem originalSourcePBWAllContractions_zero_implies_no_occupied_labels
    (x : E)
    (hzero : ∀ j : Source48Label,
      CliffordAlgebra.contractLeft (Q := Q0)
        (LinearMap.proj j : Module.Dual ℝ Source48Vector) x = 0) :
    FCP.BFSSS1V52K1D2E4.originalSourcePBWOccupiedLabels x = ∅ := by
  classical
  let occ := FCP.BFSSS1V52K1D2E4.originalSourcePBWOccupiedLabels x
  by_contra hnot
  have hocc : occ.Nonempty := Finset.nonempty_iff_ne_empty.mpr hnot
  let j : Source48Label := occ.min' hocc
  have hjocc : j ∈ occ := Finset.min'_mem occ hocc
  have hsome : ∃ I ∈ (B.repr x).support, j ∈ I := by
    simpa only [occ,
      FCP.BFSSS1V52K1D2E4.originalSourcePBWOccupiedLabels,
      Finset.mem_filter, Finset.mem_univ, true_and] using hjocc
  obtain ⟨I, hI, hjI⟩ := hsome
  have hleast : ∀ (J : Finset Source48Label),
      J ∈ (B.repr x).support →
      ∀ (k : Source48Label), k ∈ J → j ≤ k := by
    intro J hJ k hk
    exact FCP.BFSSS1V52K1D2E4.originalSourcePBWLeastOccupied_le_every_supported_coordinate
      x hocc J hJ k hk
  have hcoeff :=
    FCP.BFSSS1V52K1D2F1.originalSourcePBWLeastContraction_coefficient
      x j hleast I hI hjI
  have hczero : B.repr x I = 0 := by
    rw [hzero j] at hcoeff
    simpa using hcoeff.symm
  exact (Finsupp.mem_support_iff.mp hI) hczero

#print axioms originalSourcePBWAllContractions_zero_implies_no_occupied_labels

end
end FCP.BFSSS1V52K1D2F2
