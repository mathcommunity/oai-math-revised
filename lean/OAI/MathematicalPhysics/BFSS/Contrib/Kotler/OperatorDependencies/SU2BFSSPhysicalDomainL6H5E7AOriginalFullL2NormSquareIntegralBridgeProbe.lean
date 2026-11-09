import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E6COriginalGaussSquaredErrorIntegralLimitProbe
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
L6H5E7A — exact ORIGINAL BFSS FullL2 2 Hilbert norm-square
is the Bochner integral of its norm-square pointwise Fock fiber.

This is a mathlib L2 inner-product identity, specialized only to
the ACTUAL original FullL2 2, Boson 2 volume and Fermion 2 fiber.
No source Fock-operator expansion, no changed SU2 action or sign.

The source-exact SU2 difference quotient has an independently
qualified squared-error integral limit (H5E6C). Identifying its
L2 representative with the literal source integrand is the
next separate obligation; not silently assumed here.

No generator-domain or BFSS spectral claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E7A
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open MeasureTheory

/-- Mathlib's genuine Bochner L² norm-square identity, proved
FIRST for an abstract complex inner-product fiber. The original
48-Majorana Fock representation is not elaborated during this proof. -/
theorem abstractComplexL2_norm_sq_eq_integral
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (μ : Measure α) (w : Lp E 2 μ) :
    ‖w‖ ^ 2 = ∫ x : α, ‖w x‖ ^ 2 ∂μ := by
  have hnorm : ‖w‖ ^ 2 = Complex.re (inner ℂ w w) :=
    norm_sq_eq_re_inner (𝕜 := ℂ) w
  have hinner :
      inner ℂ w w = ∫ x : α, inner ℂ (w x) (w x) ∂μ :=
    L2.inner_def w w
  have hre :
      Complex.re (∫ x : α, inner ℂ (w x) (w x) ∂μ) =
        ∫ x : α, Complex.re (inner ℂ (w x) (w x)) ∂μ :=
    (integral_re (L2.integrable_inner (𝕜 := ℂ) w w)).symm
  have hpoint (x : α) :
      Complex.re (inner ℂ (w x) (w x)) = ‖w x‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (w x)).symm
  calc
    ‖w‖ ^ 2 = Complex.re (inner ℂ w w) := hnorm
    _ = Complex.re (∫ x : α, inner ℂ (w x) (w x) ∂μ) :=
      congrArg Complex.re hinner
    _ = ∫ x : α, Complex.re (inner ℂ (w x) (w x)) ∂μ := hre
    _ = ∫ x : α, ‖w x‖ ^ 2 ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)

/-- Norm square in the original FullL2 2 Hilbert space is exactly
the integral over the ORIGINAL bosonic volume of its genuine
Fock-fiber pointwise norm square. -/
theorem actualOriginalFullL2_norm_sq_eq_integral
    (w : FullL2 2) :
    ‖w‖ ^ 2 =
      ∫ x : Boson 2, ‖w x‖ ^ 2 ∂(volume : Measure (Boson 2)) := by
  -- #306: direct field inference and congr forced expensive concrete
  -- source Fock elaboration. Reuse the abstract compiled result;
  -- preserve the exact actual FullL2 space and bosonic volume.
  exact abstractComplexL2_norm_sq_eq_integral
    (μ := (volume : Measure (Boson 2))) w

#print axioms abstractComplexL2_norm_sq_eq_integral
#print axioms actualOriginalFullL2_norm_sq_eq_integral
#check @actualOriginalFullL2_norm_sq_eq_integral

end
end FCP.BFSSSU2PhysicalDomainL6H5E7A
