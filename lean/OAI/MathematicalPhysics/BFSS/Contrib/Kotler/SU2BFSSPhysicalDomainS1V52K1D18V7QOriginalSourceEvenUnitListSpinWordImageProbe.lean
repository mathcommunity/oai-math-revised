import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7POriginalSourceSOEuclideanGroupHomBridgeProbe
import Mathlib.Data.List.Induction
import Mathlib.Algebra.Ring.Parity

/-!
K1D18V7Q — actual original source Spin(48) group word for
an arbitrary EVEN ordered list of native SAME-48-label unit
hyperplane reflections.

V7P is strictly accepted: the ORIGINAL sourceSO transport,
defined using the existing original-Q isometry witnesses, is
an actual MonoidHom to native Euclidean LinearIsometryEquiv.
V7O is strictly accepted: the ACTUAL original Clifford-based
two-Q-unit Spin element, using the exact V7M inverse normal
transport, maps to the ordered pair of native hyperplane
reflections under the ORIGINAL source Spin-to-sourceSO hom.

The new bounded step is induction over an EVEN list, pairing
the first two unit normals and recursively using the tail
witness. The Spin witness is an actual spinGroup source-Q
element, not a substitute SO matrix or hypothetical lift.
The proof preserves the exact original list order.
This is NOT YET sourceSO generation or surjectivity:
the conclusion concerns the transport of the constructed
Spin image, not equality with an arbitrary sourceSO element.

CANDIDATE pending 46 fresh warning-as-error modules,
155 independent source exact declaration/axiom roots and
81 sealed original ancestry roots.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7Q
noncomputable section
open FCP.BFSSS1V0
open Submodule

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev SourceSO :=
  FCP.BFSSS1V52K1D18R.source48SpecialOrthogonalWitnessGL
private abbrev Euc48 := EuclideanSpace ℝ Source48Label
private abbrev sourceSOHom : spinGroup Q →* SourceSO :=
  FCP.BFSSS1V52K1D18S.originalSourceSpin48SpecialOrthogonalWitnessRepresentation
private abbrev transport : SourceSO →* (Euc48 ≃ₗᵢ[ℝ] Euc48) :=
  FCP.BFSSS1V52K1D18V7P.originalSourceSO_toEuclideanHom

/-- For EVERY genuine even-length ordered list of norm-one
vectors in the same original 48-label Euclidean target, the
native hyperplane reflection product is the transported image
of an ACTUAL original Clifford Spin(48) element. Pairing respects
Mathlib List.prod order and the ORIGINAL source Spin-to-SO action.
This is independent of any sourceSO generation assumption. -/
theorem originalSourceEvenUnitList_hasSpinWordImage
    (l : List Euc48) :
    (∀ u ∈ l, ‖u‖ = 1) →
    Even l.length →
    ∃ s : spinGroup Q,
      transport (sourceSOHom s) =
        (l.map fun u => (ℝ ∙ u)ᗮ.reflection).prod := by
  induction l using List.twoStepInduction with
  | nil =>
      intro _ _
      refine ⟨1, ?_⟩
      change transport (sourceSOHom (1 : spinGroup Q)) = 1
      simp
  | singleton u =>
      intro _ heven
      norm_num at heven
  | cons_cons u v tail ih _ =>
      intro hall heven
      have hu : ‖u‖ = 1 := hall u (by simp)
      have hv : ‖v‖ = 1 := hall v (by simp)
      have htail : ∀ z ∈ tail, ‖z‖ = 1 := by
        intro z hz
        exact hall z (by simp [hz])
      have hlen : (u :: v :: tail).length = tail.length + 2 := by
        simp only [List.length_cons]
      have htailEven : Even tail.length := by
        rw [hlen] at heven
        simpa [Nat.even_add] using heven
      rcases ih htail htailEven with ⟨t, ht⟩
      let pair : spinGroup Q :=
        FCP.BFSSS1V52K1D18V6C.originalSourceUnitPairSpin
          (FCP.BFSSS1V52K1D18V7M.originalSourceUnitNormal u)
          (FCP.BFSSS1V52K1D18V7M.originalSourceUnitNormal v)
          (FCP.BFSSS1V52K1D18V7M.originalSourceUnitNormal_Q_one u hu)
          (FCP.BFSSS1V52K1D18V7M.originalSourceUnitNormal_Q_one v hv)
      have hpair :
          transport (sourceSOHom pair) =
            (ℝ ∙ u)ᗮ.reflection * (ℝ ∙ v)ᗮ.reflection :=
        FCP.BFSSS1V52K1D18V7O.originalSourceSpinPairSO_toEuclidean_nativePair
          u v hu hv
      refine ⟨pair * t, ?_⟩
      calc
        transport (sourceSOHom (pair * t)) =
            transport (sourceSOHom pair) * transport (sourceSOHom t) := by
              simp only [map_mul]
        _ = ((ℝ ∙ u)ᗮ.reflection * (ℝ ∙ v)ᗮ.reflection) *
              ((tail.map fun z => (ℝ ∙ z)ᗮ.reflection).prod) := by
                rw [hpair, ht]
        _ = (((u :: v :: tail).map fun z => (ℝ ∙ z)ᗮ.reflection).prod) := by
              rfl

#print axioms originalSourceEvenUnitList_hasSpinWordImage

end
end FCP.BFSSS1V52K1D18V7Q
