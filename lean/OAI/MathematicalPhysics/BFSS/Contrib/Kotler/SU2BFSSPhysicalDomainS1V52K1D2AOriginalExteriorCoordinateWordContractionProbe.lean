import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V0StandaloneOrthogonalGeometryProbe
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-! Owner FCP source-only port, original cc608e2282e1b32bb11bbb64424e4775b28138e2; Git blob 6797e53e43abf6e94c76612f91617169e224e831.
Imports alone have been restructured; theorem statements/proof bodies unchanged.
The omitted original Spin ancestry is not claimed qualified by this port.
Status: provisional pending fresh owner strict-gate acceptance. -/

/-!
K1D2A — original source 48-label coordinate exterior word contraction.

The literal original Source48Label is Fin 24 × Fin 2, with source
coordinate vectors Pi.single j 1. We prove two reusable contraction
identities on finite words without a guessed spinor-majorana flattening,
external dual spaces, or exponential finite enumeration.

These lemmas are prerequisites for the exact F20B ordered exterior
basis coefficient-separation theorem, which is STILL OPEN. No
scalar-commutant, Spin48 kernel, covering, Spin9, or BFSS spectral
claim is made here. Staged until strict pinned Lean acceptance.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52K1D2A
noncomputable section
open FCP.BFSSS1V0

private abbrev E := ExteriorAlgebra ℝ Source48Vector
private abbrev Q0 : QuadraticForm ℝ Source48Vector := 0

/-- The exact exterior product of a finite ordered list of genuine
source Majorana coordinate vectors, including the empty product. -/
def originalExteriorCoordinateWord (xs : List Source48Label) : E :=
  (xs.map (fun k =>
    ExteriorAlgebra.ι ℝ (Pi.single k (1 : ℝ) : Source48Vector))).prod

theorem originalExteriorCoordinateWord_cons (k : Source48Label)
    (xs : List Source48Label) :
    originalExteriorCoordinateWord (k :: xs) =
      ExteriorAlgebra.ι ℝ (Pi.single k (1 : ℝ) : Source48Vector) *
        originalExteriorCoordinateWord xs := by
  simp [originalExteriorCoordinateWord]

/-- The original j-th coordinate contraction vanishes on any
ordered coordinate word that does not contain label j. -/
theorem originalExteriorCoordinateWord_contraction_zero_of_not_mem
    (j : Source48Label) (xs : List Source48Label) (hj : j ∉ xs) :
    CliffordAlgebra.contractLeft (Q := Q0)
      (LinearMap.proj j : Module.Dual ℝ Source48Vector)
      (originalExteriorCoordinateWord xs) = 0 := by
  induction xs with
  | nil =>
      simp [originalExteriorCoordinateWord, CliffordAlgebra.contractLeft_one]
  | cons k ks ih =>
      have hjk : j ≠ k := by
        intro h
        exact hj (by simp [h])
      have hks : j ∉ ks := by
        intro h
        exact hj (by simp [h])
      rw [originalExteriorCoordinateWord_cons]
      rw [CliffordAlgebra.contractLeft_ι_mul]
      have hcoord :
          (LinearMap.proj j : Module.Dual ℝ Source48Vector)
            (Pi.single k (1 : ℝ) : Source48Vector) = 0 := by
        simp [hjk]
      rw [hcoord, ih hks]
      simp

/-- A matching first source Majorana coordinate contracts to the
remaining original word, provided that coordinate is absent from
the tail. The scalar is exactly one (no spurious factor two). -/
theorem originalExteriorCoordinateWord_leading_contraction
    (j : Source48Label) (xs : List Source48Label) (hj : j ∉ xs) :
    CliffordAlgebra.contractLeft (Q := Q0)
      (LinearMap.proj j : Module.Dual ℝ Source48Vector)
      (originalExteriorCoordinateWord (j :: xs)) =
        originalExteriorCoordinateWord xs := by
  rw [originalExteriorCoordinateWord_cons]
  rw [CliffordAlgebra.contractLeft_ι_mul]
  have hcoord :
      (LinearMap.proj j : Module.Dual ℝ Source48Vector)
        (Pi.single j (1 : ℝ) : Source48Vector) = 1 := by
    simp
  rw [hcoord,
    originalExteriorCoordinateWord_contraction_zero_of_not_mem j xs hj]
  simp

#print axioms originalExteriorCoordinateWord_cons
#print axioms originalExteriorCoordinateWord_contraction_zero_of_not_mem
#print axioms originalExteriorCoordinateWord_leading_contraction

end
end FCP.BFSSS1V52K1D2A
