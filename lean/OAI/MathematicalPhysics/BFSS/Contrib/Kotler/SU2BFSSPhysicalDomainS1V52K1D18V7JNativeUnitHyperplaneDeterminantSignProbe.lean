import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7INativeCartanZeroFreeUnitNormalListProbe
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
K1D18V7J — pinned native unit-hyperplane reflection determinant sign.

Use exactly the accepted same-label EuclideanSpace target and the
actual Mathlib Submodule hyperplane reflection used in V7G/H/I.

The pinned Mathlib determinant formula is
  Submodule.det_reflection K :
    LinearMap.det K.reflection.toLinearMap =
      (-1) ^ Module.finrank ℝ Kᗮ.
For K = (ℝ ∙ u)ᗮ, accepted native double-orthogonal equality
and the one-dimensional nonzero span theorem reduce it to -1.

No determinant parity for Cartan lists is claimed here: the next
typed obligation is multiplicativity across List.prod followed
by evenness for transported original sourceSO. This probe does
not construct sourceSO generation, Spin48 surjectivity, covering,
global Spin9 or physical BFSS spectral existence.
Candidate until independent pinned strict CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7J
noncomputable section
open FCP.BFSSS1V0
open Submodule

private abbrev Euc48 := EuclideanSpace ℝ Source48Label

/-- A unit normal in the SAME 48-label Euclidean coordinates
is nonzero; this is the exact premise of the pinned finrank
singleton-span theorem, not an assumed nondegeneracy property. -/
theorem euclideanUnitNormal_ne_zero
    (u : Euc48) (hu : ‖u‖ = 1) : u ≠ 0 := by
  intro h
  simp [h] at hu

/-- A genuine real line spanned by a unit normal has dimension
one. This is the precise codimension-one bridge required by
the native hyperplane reflection determinant formula. -/
theorem euclideanUnitLine_finrank_one
    (u : Euc48) (hu : ‖u‖ = 1) :
    Module.finrank ℝ (ℝ ∙ u) = 1 := by
  exact finrank_span_singleton (euclideanUnitNormal_ne_zero u hu)

/-- In the ACTUAL same-label Euclidean target, each native
hyperplane reflection about a unit normal has determinant -1,
with no substitute matrix, abstract factor or unproved
orientation assumption. -/
theorem euclideanUnitHyperplane_reflection_det_neg_one
    (u : Euc48) (hu : ‖u‖ = 1) :
    LinearMap.det ((ℝ ∙ u)ᗮ.reflection.toLinearMap) = (-1 : ℝ) := by
  have hline : (ℝ ∙ u : Submodule ℝ Euc48)ᗮᗮ =
      (ℝ ∙ u : Submodule ℝ Euc48) :=
    Submodule.orthogonal_orthogonal (ℝ ∙ u : Submodule ℝ Euc48)
  have hdim : Module.finrank ℝ ((ℝ ∙ u)ᗮᗮ) = 1 := by
    calc
      Module.finrank ℝ ((ℝ ∙ u)ᗮᗮ) =
          Module.finrank ℝ (ℝ ∙ u) :=
        congrArg (fun K : Submodule ℝ Euc48 => Module.finrank ℝ K) hline
      _ = 1 := euclideanUnitLine_finrank_one u hu
  have hd := Submodule.det_reflection ((ℝ ∙ u)ᗮ)
  calc
    LinearMap.det ((ℝ ∙ u)ᗮ.reflection.toLinearMap) =
        (-1 : ℝ) ^ Module.finrank ℝ ((ℝ ∙ u)ᗮᗮ) := hd
    _ = (-1 : ℝ) := by rw [hdim, pow_one]

#print axioms euclideanUnitNormal_ne_zero
#print axioms euclideanUnitLine_finrank_one
#print axioms euclideanUnitHyperplane_reflection_det_neg_one

end
end FCP.BFSSS1V52K1D18V7J
