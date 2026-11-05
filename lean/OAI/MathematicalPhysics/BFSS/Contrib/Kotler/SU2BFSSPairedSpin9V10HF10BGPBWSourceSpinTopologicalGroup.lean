import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BFPBWCliffordTopologicalRing
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

/-!
F10BG — topological group structure on the exact source Spin9 carrier
with its inherited accepted PBW-coordinate topology.

Candidate only until the strict compiler and independent type/axiom audit pass.
The source group is the existing spinGroup source9Quadratic; no carrier,
group operation or topology is replaced. Inversion is Clifford star, and
evenness identifies it with the accepted real-linear grade reversal.

No charted space, manifold, Lie group, smoothness, differential comparison,
kernel classification, covering, Spin lift, Fock realization, gauge-domain
compatibility or BFSS spectral consequence is asserted.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum

local instance f10bgLocalNormedAddCommGroup : NormedAddCommGroup (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedAddCommGroup

local instance f10bgLocalNormedSpace : NormedSpace ℝ (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedSpace

local instance f10bgLocalFiniteDimensional : FiniteDimensional ℝ (CliffordAlgebra source9Quadratic) :=
  source9Clifford_finiteDimensional

/-- Real-linear Clifford grade reversal is continuous for the accepted PBW topology. -/
theorem source9Clifford_reverse_continuous_pbw :
    Continuous (CliffordAlgebra.reverse :
      CliffordAlgebra source9Quadratic → CliffordAlgebra source9Quadratic) := by
  exact (CliffordAlgebra.reverse :
    CliffordAlgebra source9Quadratic →ₗ[ℝ] CliffordAlgebra source9Quadratic).continuous_of_finiteDimensional

/-- The existing source Spin9 inverse, coerced to the Clifford algebra, is grade reversal. -/
theorem source9Spin_inv_coe_eq_reverse
    (g : spinGroup source9Quadratic) :
    ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic) =
      CliffordAlgebra.reverse (g : CliffordAlgebra source9Quadratic) := by
  change star (g : CliffordAlgebra source9Quadratic) =
    CliffordAlgebra.reverse (g : CliffordAlgebra source9Quadratic)
  rw [CliffordAlgebra.star_def, spinGroup.involute_eq g.property]

/-- The actual source Spin9 inverse is continuous for the inherited PBW topology. -/
theorem source9Spin_inv_continuous_pbw :
    Continuous (fun g : spinGroup source9Quadratic => g⁻¹) := by
  have heq :
      (fun g : spinGroup source9Quadratic =>
        ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic)) =
      (fun g : spinGroup source9Quadratic =>
        CliffordAlgebra.reverse (g : CliffordAlgebra source9Quadratic)) := by
    funext g
    exact source9Spin_inv_coe_eq_reverse g
  have hcoerced : Continuous (fun g : spinGroup source9Quadratic =>
      ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic)) := by
    rw [heq]
    exact source9Clifford_reverse_continuous_pbw.comp continuous_subtype_val
  exact continuous_induced_rng.2 hcoerced

/-- The actual source Spin9 multiplication is jointly continuous for the inherited PBW topology. -/
theorem source9Spin_mul_continuous_pbw :
    Continuous (fun gh : spinGroup source9Quadratic × spinGroup source9Quadratic =>
      gh.1 * gh.2) := by
  have hpair : Continuous (fun gh : spinGroup source9Quadratic × spinGroup source9Quadratic =>
      ((gh.1 : CliffordAlgebra source9Quadratic), (gh.2 : CliffordAlgebra source9Quadratic))) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hcoerced : Continuous (fun gh : spinGroup source9Quadratic × spinGroup source9Quadratic =>
      ((gh.1 * gh.2 : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic)) := by
    change Continuous (fun gh : spinGroup source9Quadratic × spinGroup source9Quadratic =>
      (gh.1 : CliffordAlgebra source9Quadratic) * (gh.2 : CliffordAlgebra source9Quadratic))
    exact source9Clifford_mul_continuous_pbw.comp hpair
  exact continuous_induced_rng.2 hcoerced

/-- The exact existing source Spin9 group is a topological group for the inherited PBW topology. -/
theorem source9Spin_isTopologicalGroup_pbw :
    IsTopologicalGroup (spinGroup source9Quadratic) where
  continuous_mul := source9Spin_mul_continuous_pbw
  continuous_inv := source9Spin_inv_continuous_pbw

#print axioms source9Clifford_reverse_continuous_pbw
#print axioms source9Spin_inv_coe_eq_reverse
#print axioms source9Spin_inv_continuous_pbw
#print axioms source9Spin_mul_continuous_pbw
#print axioms source9Spin_isTopologicalGroup_pbw

end
end FCP.BFSSPairedSpin9Clifford
