import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7NOriginalSourceSpinInverseUnitPairActionProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7AOriginalSourceSOImageGenerationBoundaryProbe

/-!
K1D18V7O — exact ORIGINAL Spin-pair SOURCE-SO image to native
Euclidean reflection-pair correspondence.

V7N is accepted: the genuine original source Clifford unit pair
at original-Q-unit inverse normal vectors acts as the ordered
native hyperplane-reflection pair.
The accepted original K1D18S spinGroup-to-sourceSO group hom and
V7D sourceSO-to-Euclidean isometry are both used unchanged.

Prove an explicit sourceSO action transport identity first, then
identify the ACTUAL sourceSO image of the ORIGINAL Spin unit pair
pointwise, then as the true LinearIsometryEquiv native product.
This proof neither defines a surrogate SO action nor assumes that
all sourceSO elements are products of pairs.

All declarations CANDIDATE until source-pinned 44-module fresh
warning-as-error compilation and independent 151-root axiom audit.
Even-list Spin word generation, unconditional image surjectivity,
covering topology, global Spin9 and BFSS spectra remain unproved.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7O
noncomputable section
open FCP.BFSSS1V0
open Submodule

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev GL48 := Source48Vector ≃ₗ[ℝ] Source48Vector
private abbrev SourceSO :=
  FCP.BFSSS1V52K1D18R.source48SpecialOrthogonalWitnessGL
private abbrev Euc48 := EuclideanSpace ℝ Source48Label
private abbrev E : Source48Vector ≃ₗ[ℝ] Euc48 :=
  FCP.BFSSS1V52K1D18V7C.originalSource48ToEuclidean
private abbrev sourceSOHom : spinGroup Q →* SourceSO :=
  FCP.BFSSS1V52K1D18S.originalSourceSpin48SpecialOrthogonalWitnessRepresentation

/-- The actual accepted V7D transported sourceSO element acts
on the original 48 labels by the SAME real-linear sourceSO map
conjugated by E. The chosen Q-isometry witness does not introduce
an extra action. -/
theorem originalSourceSO_toEuclideanIsometry_exactAction
    (g : SourceSO) (w : Source48Vector) :
    FCP.BFSSS1V52K1D18V7D.sourceSO_toEuclideanIsometry g (E w) =
      E ((g : GL48) w) := by
  have hco :
      E (((FCP.BFSSS1V52K1D18V7D.sourceSO_originalQIsometry g :
        GL48)) w) = E ((g : GL48) w) :=
    congrArg (fun f : GL48 => E (f w))
      (FCP.BFSSS1V52K1D18V7D.sourceSO_originalQIsometry_underlying g)
  calc
    FCP.BFSSS1V52K1D18V7D.sourceSO_toEuclideanIsometry g (E w) =
        E ((FCP.BFSSS1V52K1D18V7D.sourceSO_originalQIsometry g :
          GL48) w) := by
          change E ((FCP.BFSSS1V52K1D18V7D.sourceSO_originalQIsometry g)
            (E.symm (E w))) =
            E ((FCP.BFSSS1V52K1D18V7D.sourceSO_originalQIsometry g) w)
          rw [E.symm_apply_apply]
    _ = E ((g : GL48) w) := hco

/-- At ANY true native Euclidean unit normals u and v, the
ACTUAL original Spin-to-sourceSO homomorphism has exactly the
ordered two-hyperplane-reflection action after V7D transport. -/
theorem originalSourceSpinPairSO_toEuclidean_exactAction
    (u v x : Euc48) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    FCP.BFSSS1V52K1D18V7D.sourceSO_toEuclideanIsometry
      (sourceSOHom
        (FCP.BFSSS1V52K1D18V6C.originalSourceUnitPairSpin
          (FCP.BFSSS1V52K1D18V7M.originalSourceUnitNormal u)
          (FCP.BFSSS1V52K1D18V7M.originalSourceUnitNormal v)
          (FCP.BFSSS1V52K1D18V7M.originalSourceUnitNormal_Q_one u hu)
          (FCP.BFSSS1V52K1D18V7M.originalSourceUnitNormal_Q_one v hv))) x =
        ((ℝ ∙ u)ᗮ.reflection * (ℝ ∙ v)ᗮ.reflection) x := by
  let s : spinGroup Q :=
    FCP.BFSSS1V52K1D18V6C.originalSourceUnitPairSpin
      (FCP.BFSSS1V52K1D18V7M.originalSourceUnitNormal u)
      (FCP.BFSSS1V52K1D18V7M.originalSourceUnitNormal v)
      (FCP.BFSSS1V52K1D18V7M.originalSourceUnitNormal_Q_one u hu)
      (FCP.BFSSS1V52K1D18V7M.originalSourceUnitNormal_Q_one v hv)
  let g : SourceSO := sourceSOHom s
  have hcoe : (g : GL48) =
      FCP.BFSSS1V52K1D13.originalSourceSpin48LinearRepresentation s :=
    FCP.BFSSS1V52K1D18S.originalSourceSpin48SpecialOrthogonalWitnessRepresentation_coe s
  have haction : (g : GL48) (E.symm x) =
      FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry s (E.symm x) := by
    change (g : GL48) (E.symm x) =
      FCP.BFSSS1V31.sourceSpin48VectorAction s (E.symm x)
    exact congrArg (fun f : GL48 => f (E.symm x)) hcoe
  calc
    FCP.BFSSS1V52K1D18V7D.sourceSO_toEuclideanIsometry g x =
        E ((g : GL48) (E.symm x)) := by
          simpa only [E.apply_symm_apply] using
            (originalSourceSO_toEuclideanIsometry_exactAction g (E.symm x))
    _ = E (FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry
          s (E.symm x)) := congrArg E haction
    _ = ((ℝ ∙ u)ᗮ.reflection * (ℝ ∙ v)ᗮ.reflection) x :=
      FCP.BFSSS1V52K1D18V7N.originalSourceSpinUnitPair_euclideanNormals_actionOnEuclidean
        u v x hu hv

/-- Full native group-element equality for a genuine original
Spin unit pair under the ACTUAL sourceSO transport. It says only
the pair image is correct, not that all sourceSO is generated. -/
theorem originalSourceSpinPairSO_toEuclidean_nativePair
    (u v : Euc48) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    FCP.BFSSS1V52K1D18V7D.sourceSO_toEuclideanIsometry
      (sourceSOHom
        (FCP.BFSSS1V52K1D18V6C.originalSourceUnitPairSpin
          (FCP.BFSSS1V52K1D18V7M.originalSourceUnitNormal u)
          (FCP.BFSSS1V52K1D18V7M.originalSourceUnitNormal v)
          (FCP.BFSSS1V52K1D18V7M.originalSourceUnitNormal_Q_one u hu)
          (FCP.BFSSS1V52K1D18V7M.originalSourceUnitNormal_Q_one v hv))) =
        (ℝ ∙ u)ᗮ.reflection * (ℝ ∙ v)ᗮ.reflection := by
  apply LinearIsometryEquiv.ext
  intro x
  exact originalSourceSpinPairSO_toEuclidean_exactAction u v x hu hv

#print axioms originalSourceSO_toEuclideanIsometry_exactAction
#print axioms originalSourceSpinPairSO_toEuclidean_exactAction
#print axioms originalSourceSpinPairSO_toEuclidean_nativePair

end
end FCP.BFSSS1V52K1D18V7O
