import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F13OriginalNativeSixteenSpin48UnitaryFockMajoranaCovarianceProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9D8OriginalFockMajorana48SourceBasisMulVecProbe

/-!
L9E5F16 — STAGED ONLY / UNQUALIFIED, no CI until predecessor
F15 gate is resolved.

An exact generator-BASIS specialization of accepted F13
Hilbert-unitary source covariance and the exact original L9D8
48-real source-matrix color coordinate law. Real coefficients
and normalized original Fermion2 Majoranas are preserved:
the original pairedTheta basis has normalization sqrt(2), so
this theorem deliberately uses real smul and normal-form
normalized operators. The subsequent unscaled pairedTheta
covariance and full physical gauge uniqueness are distinct.

No global odd Clifford star law, swapped color indices,
independent Spin48 unitary, or BFSS spectrum assertion.
-/

set_option autoImplicit false
set_option maxHeartbeats 360000

namespace FCP.BFSSS1V52L9E5F16
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L8E
open FCP.BFSSS1V52L9E2
open FCP.BFSSS1V52L9E4
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5F13
open FCP.BFSSS1V52L9D8
open FCP.BFSSSU2GaugeG3A

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- Genuine original native sixteen-block source Spin48 Fock
image rotates every normalized original Fock Majorana color
axis with the ACTUAL original output-B/input-A real
adjointColorMatrix, as a Hilbert-adjoint conjugation. -/
theorem originalNativeSixteenFock_normalizedMajorana_color_covariance
    (g : GaugeGroup 2) (α : RealSpinBlock) (A : Fin 3) :
    originalFockCliffordAlgHom
        (((originalNativeSixteenSpinHom g : spinGroup Q) : C)) *
      originalNormalizedFockMajorana α A *
      star (originalFockCliffordAlgHom
        (((originalNativeSixteenSpinHom g : spinGroup Q) : C))) =
      ∑ B : Fin 3, (adjointColorMatrix g B A) •
        originalNormalizedFockMajorana α B := by
  have h := originalNativeSixteenSpinFock_unitary_majorana_covariance
    g (sourceBlockColorAxis α A)
  rw [originalFockGammaRealLinear_sourceAxis] at h
  rw [originalSourceRealMajoranaMatrix_mulVec_sourceAxis] at h
  simpa only [map_sum, map_smul,
    originalFockGammaRealLinear_sourceAxis] using h

-- Qualified original-source imported lemmas, independently checked
-- here but NOT counted as new F16 roots.
#print axioms FCP.BFSSS1V52L9D8.originalSourceRealMajoranaMatrix_mulVec_sourceAxis
#print axioms FCP.BFSSS1V52L9E4.originalFockGammaRealLinear_sourceAxis
#print axioms originalNativeSixteenFock_normalizedMajorana_color_covariance

end
end FCP.BFSSS1V52L9E5F16
