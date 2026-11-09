import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10TSourceSpin9NegativeCentralMembershipProbe

/-!
K1D18V10H-F10U — ACTUAL nontrivial negative central source Spin9
image under the accepted algebraic original G1A paired-label SO48 map.

F10S accepts the negative Clifford scalar's conditional image.
F10T constructs a GENUINE Mathlib source spinGroup member with
underlying Clifford value -1. Compose the two, then evaluate the
original paired 48-label matrix on a source diagonal coordinate
to show the image is not the identity. The source 48-label ordering
and original sixteen-real gamma matrices are unchanged.

This proves nontriviality on the central negative scalar, NOT an
entire kernel classification, faithful Spin9 representation,
Spin48 lift, topological covering, Fock implementation, gauge
intertwiner, or physical BFSS spectral claim.

CANDIDATE until pinned strict warning-as-error compilation and
four independently elaborated theorem types/axiom audits pass.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- Discharge F10S's genuine-source-element premise using the
newly ACCEPTED F10T actual negative central source Spin9 member.
The result acts on ORIGINAL paired Fock 48 real labels. -/
theorem source9NegativeCentral_originalPairedSO48_image :
    ((source9SpinOriginalPaired48SpecialOrthogonalHom
        source9NegativeCentral) :
      Matrix Source48Label Source48Label ℝ) =
    -(1 : Matrix Source48Label Source48Label ℝ) := by
  exact source9SpinOriginalPaired48SOHom_neg_scalar_of_mem
    source9NegativeCentral source9NegativeCentral_coe

/-- ACTUAL source Spin9 negative central element has nonidentity
SO(original paired-48) action. Evaluate the exact diagonal
original Source48Label coordinate, not a color-major surrogate. -/
theorem source9NegativeCentral_originalPairedSO48_image_ne_one :
    source9SpinOriginalPaired48SpecialOrthogonalHom
      source9NegativeCentral ≠ 1 := by
  intro h
  have hmat : ((source9SpinOriginalPaired48SpecialOrthogonalHom
      source9NegativeCentral) :
      Matrix Source48Label Source48Label ℝ) =
      (1 : Matrix Source48Label Source48Label ℝ) :=
    congrArg (fun M : Matrix.specialOrthogonalGroup Source48Label ℝ =>
      (M : Matrix Source48Label Source48Label ℝ)) h
  rw [source9NegativeCentral_originalPairedSO48_image] at hmat
  have hdiag := congrArg
    (fun M : Matrix Source48Label Source48Label ℝ =>
      M ((0 : Fin 24), (0 : Fin 2)) ((0 : Fin 24), (0 : Fin 2)))
    hmat
  norm_num at hdiag

/-- The genuine negative central source Spin9 element is NOT
in the kernel of the original paired-label SO48 action.
This gives a single explicit obstruction, not full kernel data. -/
theorem source9NegativeCentral_not_mem_originalPairedSO48_ker :
    source9NegativeCentral ∉
      source9SpinOriginalPaired48SpecialOrthogonalHom.ker := by
  intro h
  apply source9NegativeCentral_originalPairedSO48_image_ne_one
  exact (MonoidHom.mem_ker).mp h

/-- The constructed original source Spin9 negative central
group element is distinct from identity, using its genuine
nontrivial original paired-label SO48 image. -/
theorem source9NegativeCentral_ne_one :
    source9NegativeCentral ≠ (1 : spinGroup source9Quadratic) := by
  intro h
  apply source9NegativeCentral_originalPairedSO48_image_ne_one
  rw [h, map_one]

#print axioms source9NegativeCentral_originalPairedSO48_image
#print axioms source9NegativeCentral_originalPairedSO48_image_ne_one
#print axioms source9NegativeCentral_not_mem_originalPairedSO48_ker
#print axioms source9NegativeCentral_ne_one

end
end FCP.BFSSPairedSpin9Clifford
