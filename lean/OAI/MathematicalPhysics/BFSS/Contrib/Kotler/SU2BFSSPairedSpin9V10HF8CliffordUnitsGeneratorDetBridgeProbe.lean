import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF7TwoSignObstructionDiscriminatorProbe

/-!
K1D18V10H-F8 — ambient Clifford-unit determinant bridge,
preparing a genuinely source-generated proof of orientation.

Prior accepted F1–F7 show exact Spin9 determinant sign and
the commutator obstruction but do not determine whether
all source group elements have determinant +1.

The original pinned Mathlib SpinGroup source defines the
Lipschitz group as closure of invertible Clifford vector
generators, and source Spin9 lies in its unitary-even part.

This experiment constructs the ACTUAL determinant character
on AMBIENT Clifford algebra units from the already-accepted
original source Clifford gamma AlgHom, then proves exact
evaluation on source Spin9 and on Clifford vector generators.
The group-hom construction is direct: source map-one and
map-mul proofs, not the unqualified nested V10H composition.

This lays out a strict future generator obligation:
the determinant sign of gammaNineRealLinear on each
invertible ORIGINAL Clifford generator. It does not
solve that generator determinant sign or prove source
group square generation/perfectness. It does not alter
the original gamma, Fock labels, or source definition.
No continuity, original Spin48 lift or BFSS physics claim.

F8 CANDIDATE pending exact strict CI.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- Direct determinant map on actual units of the exact
nine-source real Clifford algebra, evaluated in the
original 16-real gamma representation. The target ℝ
is a multiplicative monoid, not the group of units. -/
noncomputable def source9CliffordUnitsGammaDetHom :
    (CliffordAlgebra source9Quadratic)ˣ →* ℝ where
  toFun u :=
    (source9GammaCliffordAlgHom
      (u : CliffordAlgebra source9Quadratic)).det
  map_one' := by
    change (source9GammaCliffordAlgHom
      ((1 : (CliffordAlgebra source9Quadratic)ˣ) :
        CliffordAlgebra source9Quadratic)).det = 1
    rw [Units.val_one, map_one, Matrix.det_one]
  map_mul' := by
    intro u v
    change (source9GammaCliffordAlgHom
      ((u * v : (CliffordAlgebra source9Quadratic)ˣ) :
        CliffordAlgebra source9Quadratic)).det =
      (source9GammaCliffordAlgHom
        (u : CliffordAlgebra source9Quadratic)).det *
      (source9GammaCliffordAlgHom
        (v : CliffordAlgebra source9Quadratic)).det
    rw [Units.val_mul, map_mul, Matrix.det_mul]

/-- Typed evaluation avoids unfolding a nested determinant
map or coercion at any original source Spin9 term. -/
theorem source9CliffordUnitsGammaDetHom_apply
    (u : (CliffordAlgebra source9Quadratic)ˣ) :
    source9CliffordUnitsGammaDetHom u =
      (source9GammaCliffordAlgHom
        (u : CliffordAlgebra source9Quadratic)).det := rfl

/-- Accepted F5 Spin9 character is exactly the restriction
of the new ambient Clifford-unit determinant map through
the *actual* pinned spinGroup.toUnits homomorphism. -/
theorem source9CliffordUnitsGammaDetHom_spin_apply
    (g : spinGroup source9Quadratic) :
    source9CliffordUnitsGammaDetHom
        (spinGroup.toUnits g) = gammaDetDirectHom g := by
  rw [source9CliffordUnitsGammaDetHom_apply,
    gammaDetDirectHom_apply, source9SpinGammaOrthogonalHom_apply]
  rfl

/-- The ACTUAL Clifford vector generator is represented by
the unchanged nine-gamma real linear combination.
Only the exact algebraic generator evaluation is asserted:
NO positivity, sign, determinant formula or invertibility
of an arbitrary original source vector is invented. -/
theorem source9CliffordUnitsGammaDetHom_generator
    (u : (CliffordAlgebra source9Quadratic)ˣ)
    (v : SpaceIndex → ℝ)
    (hvec : (u : CliffordAlgebra source9Quadratic) =
      CliffordAlgebra.ι source9Quadratic v) :
    source9CliffordUnitsGammaDetHom u =
      (gammaNineRealLinear v).det := by
  rw [source9CliffordUnitsGammaDetHom_apply,
    hvec, source9GammaCliffordAlgHom_generator]

#print axioms source9CliffordUnitsGammaDetHom
#print axioms source9CliffordUnitsGammaDetHom_apply
#print axioms source9CliffordUnitsGammaDetHom_spin_apply
#print axioms source9CliffordUnitsGammaDetHom_generator

end
end FCP.BFSSPairedSpin9DetFixture
