import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10OCliffordUnitGeneratorPositivityProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

/-!
K1D18V10H-F10P — determinant positivity on ACTUAL source Lipschitz units.

Pinned Mathlib SpinGroup.lean defines
  lipschitzGroup Q := Subgroup.closure ((↑) ⁻¹' Set.range (ι Q))
as a subgroup of the units of the original Clifford algebra.

F10O strictly qualified that the actual source Clifford-unit real
determinant monoid hom is positive on each source invertible vector
generator and that positivity is preserved by inverses. Positivity
is also preserved by multiplication and holds for one.

Two independent source-typed obligations:
* use PINNED Subgroup.closure_induction'' to establish strict
  positivity on EVERY actual original lipschitzGroup Q unit;
* transport to every genuine source spinGroup Q term through
  pinned spinGroup.toUnits, spinGroup.units_mem_lipschitzGroup,
  and qualified F8 source9CliffordUnitsGammaDetHom_spin_apply.

This stage does NOT assert that the Spin9 determinant equals 1
or that its orientation subgroup is top. Those require a separate
exact type/axiom gate combining the accepted determinant-square-one
with this new strict positivity. Fock-ordered 48-fermion covariance,
Spin48 lift/cover, and BFSS physical spectrum remain independent.

No private gamma tables, new axioms, changed source indexing,
altered compiler warning rules or artificial resource limits.
Unqualified until strict warning-as-error and two independent audits.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- Exact source Clifford-unit determinant positivity extends to
EVERY member of pinned Mathlib's genuine generated Lipschitz group. -/
theorem source9CliffordUnitsGammaDetHom_pos_of_mem_lipschitzGroup
    (u : (CliffordAlgebra source9Quadratic)ˣ)
    (hu : u ∈ lipschitzGroup source9Quadratic) :
    0 < source9CliffordUnitsGammaDetHom u := by
  unfold lipschitzGroup at hu
  induction hu using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨v, hv⟩ := hx
    exact source9CliffordUnitsGammaDetHom_pos_generator x v hv.symm
  | inv_mem x hx =>
    obtain ⟨v, hv⟩ := hx
    exact source9CliffordUnitsGammaDetHom_pos_inv_of_pos x
      (source9CliffordUnitsGammaDetHom_pos_generator x v hv.symm)
  | one =>
    simp
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact mul_pos hx hy

/-- The accepted original Spin9 determinant character is strictly
positive on EVERY genuine source spinGroup element, via the
PINNED source SpinGroup.toUnits and Lipschitz membership bridge. -/
theorem gammaDetDirectHom_pos_of_source_spinGroup
    (g : spinGroup source9Quadratic) :
    0 < gammaDetDirectHom g := by
  have hx :
      ((spinGroup.toUnits g : (CliffordAlgebra source9Quadratic)ˣ) :
        CliffordAlgebra source9Quadratic) ∈
        spinGroup source9Quadratic := by
    exact g.property
  have hu :
      spinGroup.toUnits g ∈ lipschitzGroup source9Quadratic :=
    spinGroup.units_mem_lipschitzGroup hx
  have hp :=
    source9CliffordUnitsGammaDetHom_pos_of_mem_lipschitzGroup
      (spinGroup.toUnits g) hu
  rw [source9CliffordUnitsGammaDetHom_spin_apply] at hp
  exact hp

#print axioms source9CliffordUnitsGammaDetHom_pos_of_mem_lipschitzGroup
#print axioms gammaDetDirectHom_pos_of_source_spinGroup

end
end FCP.BFSSPairedSpin9DetFixture
