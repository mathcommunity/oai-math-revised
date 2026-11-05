import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10YSourceNineCliffordPBWBasisProbe
import Mathlib.Data.Finset.Sort

/-!
K1D18V10H-F10Z — exact original source NINE-coordinate
exterior PBW words and Clifford/exterior transport.

This specializes the original FCP K1D2C ordered-source PBW
word construction to ACTUAL SpaceIndex (Fin 9), using F10Y's
accepted Clifford PBW basis for source9Quadratic.

The exterior product identity is established in the ORIGINAL
source coordinate basis. The Clifford/exterior equivalence
remains REAL LINEAR, not multiplicative. We make NO claim
that its Clifford image equals an arbitrary unqualified
noncommutative gamma matrix word.

This sets up a source-exact word/coordinate interface for
subsequent EVEN Clifford gamma-image coefficient isolation.
It does NOT prove even gamma injectivity, entire Spin9
faithfulness, original Spin48 lift, or BFSS physical physics.

CANDIDATE until pinned strict warning-as-error compilation
and independent exact type/axiom qualification.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum

private abbrev E9 := ExteriorAlgebra ℝ (SpaceIndex → ℝ)

/-- ACTUAL source nine-coordinate exterior PBW basis. -/
noncomputable def source9ExteriorPBWBasis :
    Module.Basis (Finset SpaceIndex) ℝ E9 :=
  (Pi.basisFun ℝ SpaceIndex).ExteriorAlgebra

/-- Original source nine-coordinate exterior algebra product
of a finite ordered coordinate-label word, including []. -/
def source9ExteriorCoordinateWord
    (xs : List SpaceIndex) : E9 :=
  (xs.map (fun k => ExteriorAlgebra.ι ℝ
    (Pi.single k (1 : ℝ) : SpaceIndex → ℝ))).prod

/-- Ordered genuine source nine-coordinate labels for each
finite subset; no new flattening or color-major choice. -/
noncomputable def source9ExteriorPBWOrderedLabels
    (I : Finset SpaceIndex) : List SpaceIndex :=
  List.ofFn (fun i : Fin I.card => I.orderEmbOfFin rfl i)

/-- PBW source exterior basis elements are EXACTLY the
ordered products of their genuine nine coordinate vectors. -/
theorem source9ExteriorPBWBasis_eq_coordinateWord
    (I : Finset SpaceIndex) :
    source9ExteriorPBWBasis I =
      source9ExteriorCoordinateWord
        (source9ExteriorPBWOrderedLabels I) := by
  classical
  change (Pi.basisFun ℝ SpaceIndex).ExteriorAlgebra I =
    source9ExteriorCoordinateWord
      (List.ofFn (fun i : Fin I.card => I.orderEmbOfFin rfl i))
  rw [ExteriorAlgebra.basis_apply]
  unfold ExteriorAlgebra.ιMulti_family
  rw [ExteriorAlgebra.ιMulti_apply]
  simp only [source9ExteriorCoordinateWord,
    Set.powersetCard.prodEquiv_symm_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply,
    List.ofFn_eq_map, List.map_map, Function.comp_apply,
    Pi.basisFun_apply]
  rfl

/-- The actual source PBW ordered coordinate labels are
pairwise distinct, as required for later coefficient
separation and contraction arguments. -/
theorem source9ExteriorPBWOrderedLabels_nodup
    (I : Finset SpaceIndex) :
    (source9ExteriorPBWOrderedLabels I).Nodup := by
  classical
  change (List.ofFn (fun i : Fin I.card =>
    I.orderEmbOfFin rfl i)).Nodup
  exact List.nodup_ofFn.mpr (I.orderEmbOfFin rfl).injective

/-- EXACT F10Y source Clifford PBW basis element,
identified through Mathlib's accepted real-LINEAR
Clifford/exterior equivalence with the source exterior
ordered coordinate word. No multiplication preservation
of equivExterior is asserted. -/
theorem source9CliffordPBWBasis_eq_exteriorWord
    (I : Finset SpaceIndex) :
    source9CliffordPBWBasis I =
      (CliffordAlgebra.equivExterior source9Quadratic).symm
        (source9ExteriorCoordinateWord
          (source9ExteriorPBWOrderedLabels I)) := by
  classical
  change
    (CliffordAlgebra.equivExterior source9Quadratic).symm
      ((Pi.basisFun ℝ SpaceIndex).ExteriorAlgebra I) =
    (CliffordAlgebra.equivExterior source9Quadratic).symm
      (source9ExteriorCoordinateWord
        (source9ExteriorPBWOrderedLabels I))
  exact congrArg
    (CliffordAlgebra.equivExterior source9Quadratic).symm
    (source9ExteriorPBWBasis_eq_coordinateWord I)

#print axioms source9ExteriorPBWBasis
#print axioms source9ExteriorCoordinateWord
#print axioms source9ExteriorPBWOrderedLabels
#print axioms source9ExteriorPBWBasis_eq_coordinateWord
#print axioms source9ExteriorPBWOrderedLabels_nodup
#print axioms source9CliffordPBWBasis_eq_exteriorWord

end
end FCP.BFSSPairedSpin9Clifford
