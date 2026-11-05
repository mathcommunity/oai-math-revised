import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BCSourceSpinGammaSpecialOrthogonalHom
import Mathlib.Topology.Algebra.Module.FiniteDimension
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10YSourceNineCliffordPBWBasisProbe
import Mathlib.Analysis.Normed.Module.TransferInstance
import Mathlib.LinearAlgebra.Finsupp.Pi

set_option autoImplicit false

open OAI.BFSSQuantum

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

/-!
F10BE — named PBW-coordinate normed structures and original gamma continuity.

Candidate promotion of successful F10BD2/F10BD3 diagnostics. The chosen
norm is induced from the finite coordinate Pi space through the exact
accepted source-nine PBW basis and Finsupp/Pi adapter.

The structures below are named values, enabled only locally in this file.
Downstream users must explicitly install those same values; no global
topology or normed-space instance is registered.

Scope: ambient and source Spin9 Hausdorff separation, continuity of the
whole-Clifford original gamma evaluation, and continuity of the existing
F10BC Spin9-to-SO16 homomorphism. No Clifford multiplication continuity,
topological-group structure, manifold, smoothness, differential comparison,
Spin lift, Fock implementation, gauge compatibility or spectral claim.
-/

local instance : Fintype (Finset SpaceIndex) := Fintype.ofFinite _

/-- The accepted PBW coordinates, expressed as a genuine finite Pi space. -/
noncomputable def source9PBWCoordinates :
    CliffordAlgebra source9Quadratic ≃ₗ[ℝ] (Finset SpaceIndex → ℝ) :=
  source9CliffordPBWBasis.repr.trans (Finsupp.linearEquivFunOnFinite ℝ ℝ (Finset SpaceIndex))

/-- The exact PBW-coordinate induced normed additive group; not a global instance. -/
@[instance_reducible]
noncomputable def source9PBWNormedAddCommGroup :
    NormedAddCommGroup (CliffordAlgebra source9Quadratic) :=
  NormedAddCommGroup.induced
    (CliffordAlgebra source9Quadratic)
    (Finset SpaceIndex → ℝ)
    source9PBWCoordinates.toAddMonoidHom
    source9PBWCoordinates.injective

attribute [local instance] source9PBWNormedAddCommGroup

/-- Real normed-space compatibility for the named PBW normed group. -/
@[instance_reducible]
noncomputable def source9PBWNormedSpace :
    NormedSpace ℝ (CliffordAlgebra source9Quadratic) :=
  NormedSpace.induced ℝ
    (CliffordAlgebra source9Quadratic)
    (Finset SpaceIndex → ℝ)
    source9PBWCoordinates

attribute [local instance] source9PBWNormedSpace

/-- The exact source Clifford algebra is Hausdorff for the named PBW topology. -/
theorem source9Clifford_t2Space_pbw :
    T2Space (CliffordAlgebra source9Quadratic) := inferInstance

/-- The exact algebraic Spin9 subtype inherits Hausdorff separation. -/
theorem source9Spin_t2Space_pbw :
    T2Space (spinGroup source9Quadratic) := inferInstance

local instance : FiniteDimensional ℝ (CliffordAlgebra source9Quadratic) :=
  source9Clifford_finiteDimensional

/-- Continuity of the exact whole-Clifford original-gamma evaluation
for the named PBW-coordinate topology and standard matrix topology. -/
theorem source9GammaCliffordAlgHom_continuous_pbw :
    Continuous source9GammaCliffordAlgHom := by
  exact source9GammaCliffordAlgHom.toLinearMap.continuous_of_finiteDimensional

/-- Continuity of the exact accepted F10BC homomorphism for the
named PBW-coordinate source topology and standard SO16 subtype topology. -/
theorem source9SpinGammaSpecialOrthogonalHom_continuous_pbw :
    Continuous source9SpinGammaSpecialOrthogonalHom := by
  have hcliff : Continuous source9GammaCliffordAlgHom :=
    source9GammaCliffordAlgHom.toLinearMap.continuous_of_finiteDimensional
  have heq :
      (fun g : spinGroup source9Quadratic =>
        ((source9SpinGammaSpecialOrthogonalHom g) : GammaMatrix)) =
      (fun g : spinGroup source9Quadratic =>
        source9GammaCliffordAlgHom (g : CliffordAlgebra source9Quadratic)) := by
    funext g
    exact source9SpinGammaSpecialOrthogonalHom_apply g
  have hmatrix : Continuous (fun g : spinGroup source9Quadratic =>
      ((source9SpinGammaSpecialOrthogonalHom g) : GammaMatrix)) := by
    rw [heq]
    exact hcliff.comp continuous_subtype_val
  exact continuous_induced_rng.2 hmatrix

#print axioms source9PBWCoordinates
#print axioms source9PBWNormedAddCommGroup
#print axioms source9PBWNormedSpace
#print axioms source9Clifford_t2Space_pbw
#print axioms source9Spin_t2Space_pbw
#print axioms source9GammaCliffordAlgHom_continuous_pbw
#print axioms source9SpinGammaSpecialOrthogonalHom_continuous_pbw

end
end FCP.BFSSPairedSpin9Clifford
