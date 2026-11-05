import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10VSourceCentralInvolutionSO48SignActionProbe

/-!
K1D18V10H-F10W — exact SOURCE Spin9 kernel reduction
from original G1A paired-Fock SO48 to original gamma16 O16.

The accepted V10F source-to-original-paired transport is
Kronecker by the genuine three-color identity, followed by the
exact G1A pairedColorSpinEquiv reindexRingEquiv. Evaluation
at an ACTUAL first color diagonal proves transport injective.

Use this injectivity to prove equality of genuine source Spin9
SO48 images IFF equality of accepted source gamma16 O16 images,
and hence exact equality of their subgroup kernels.

This does NOT establish faithfulness of the gamma16
representation, classify the source gamma kernel, construct
a Spin48 lift/cover, Fock action, gauge theorem, or BFSS
spectral physics. It avoids alternate color-major labels.

CANDIDATE pending strict warning-as-error Lean and
independently elaborated four declaration type/axiom checks.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSPairedSpin9Plane
open OAI.BFSSQuantum
open Matrix
open scoped Kronecker

/-- The accepted original three-color identity-Kronecker,
then actual G1A paired-label reindexing, is injective on
the ORIGINAL sixteen-real gamma matrix algebra. -/
theorem gamma16ToOriginalPaired48_injective :
    Function.Injective gamma16ToOriginalPaired48 := by
  intro A B h
  let E := Matrix.reindexRingEquiv ℝ pairedColorSpinEquiv
  have hK :
      ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ A) =
      ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ B) := by
    apply E.injective
    change gamma16ToOriginalPaired48 A =
      gamma16ToOriginalPaired48 B
    exact h
  ext i j
  have hij := congrArg
    (fun M : Matrix (ColorIndex 2 × SpinIndex)
        (ColorIndex 2 × SpinIndex) ℝ =>
      M ((⟨0, by decide⟩ : ColorIndex 2), i)
        ((⟨0, by decide⟩ : ColorIndex 2), j)) hK
  simpa [Matrix.kronecker_apply] using hij

/-- Equality of actual Spin9 original paired SO48 images is
EQUIVALENT to equality of the actual gamma16 O16 images.
Neither direction assumes image injectivity of source Spin9. -/
theorem source9OriginalPairedSO48_eq_iff_gamma16
    (g h : spinGroup source9Quadratic) :
    source9SpinOriginalPaired48SpecialOrthogonalHom g =
      source9SpinOriginalPaired48SpecialOrthogonalHom h ↔
    source9SpinGammaOrthogonalHom g =
      source9SpinGammaOrthogonalHom h := by
  constructor
  · intro heq
    have hmat := congrArg
      (fun M : Matrix.specialOrthogonalGroup Source48Label ℝ =>
        (M : Matrix Source48Label Source48Label ℝ)) heq
    change gamma16ToOriginalPaired48
      ((source9SpinGammaOrthogonalHom g) : GammaMatrix) =
        gamma16ToOriginalPaired48
          ((source9SpinGammaOrthogonalHom h) : GammaMatrix) at hmat
    apply Subtype.ext
    exact gamma16ToOriginalPaired48_injective hmat
  · intro heq
    apply Subtype.ext
    change gamma16ToOriginalPaired48
      ((source9SpinGammaOrthogonalHom g) : GammaMatrix) =
        gamma16ToOriginalPaired48
          ((source9SpinGammaOrthogonalHom h) : GammaMatrix)
    rw [heq]

/-- Original paired SO48 kernel membership is equivalent to
membership in the exact genuine source gamma16 O16 kernel. -/
theorem source9OriginalPairedSO48_mem_ker_iff_gamma16
    (g : spinGroup source9Quadratic) :
    g ∈ source9SpinOriginalPaired48SpecialOrthogonalHom.ker ↔
      g ∈ source9SpinGammaOrthogonalHom.ker := by
  simpa only [MonoidHom.mem_ker, map_one] using
    (source9OriginalPairedSO48_eq_iff_gamma16 g 1)

/-- Exact equality of source Spin9 subgroup kernels; this
reduces a larger-index kernel obligation, not the original
gamma16 kernel itself. -/
theorem source9OriginalPairedSO48_ker_eq_gamma16_ker :
    (source9SpinOriginalPaired48SpecialOrthogonalHom.ker :
      Set (spinGroup source9Quadratic)) =
    (source9SpinGammaOrthogonalHom.ker :
      Set (spinGroup source9Quadratic)) := by
  ext g
  exact source9OriginalPairedSO48_mem_ker_iff_gamma16 g

#print axioms gamma16ToOriginalPaired48_injective
#print axioms source9OriginalPairedSO48_eq_iff_gamma16
#print axioms source9OriginalPairedSO48_mem_ker_iff_gamma16
#print axioms source9OriginalPairedSO48_ker_eq_gamma16_ker

end
end FCP.BFSSPairedSpin9Clifford
