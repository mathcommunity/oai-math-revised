import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7YActualSourceFullL2CombinedGaugeGroupLawProbe

/-!
L6G7Z — the genuine original BFSS GaugeData source action on
FullL2 2 is an EXACT complex-linear unitary representation of
SU(2), assembled from independently qualified source theorems.

L6G7U defines the exact original GaugeCore U(g)=fiberAction(g) ∘
bosonPullback(g⁻¹); L6G7W proves global FullL2 norm preservation;
L6G7Y proves U(g)U(h)=U(gh) and U(1)=id. The group inverse is
therefore the literal U(g⁻¹), so source U(g) is a surjective
complex-linear isometry. Package it in a LinearIsometryEquiv and
then a MonoidHom, using no proxy space or new hypothesis.

This supplies the exact Hilbert-unitary SU2 representation,
but does NOT claim strong g-continuity, an infinitesimal
unbounded Gauss generator, essential self-adjointness, or
spectral conclusions. Exact +i and -i source signs unchanged.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace FCP.BFSSSU2PhysicalDomainL6G7Z
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6G7W
open FCP.BFSSSU2PhysicalDomainL6G7Y

/-- Original source FullL2 group inverse cancels the TRUE gauge map
on the left, not merely on a smooth core or auxiliary Fock space. -/
theorem actualOriginalFullL2GaugePair_inv_left
    (g : GaugeGroup 2) (v : FullL2 2) :
    actualOriginalFullL2GaugePairCLM g⁻¹
      (actualOriginalFullL2GaugePairCLM g v) = v := by
  rw [actualOriginalFullL2GaugePair_mul,
    inv_mul_cancel, actualOriginalFullL2GaugePair_one]

/-- Actual original FullL2 source gauge inverse on the right. -/
theorem actualOriginalFullL2GaugePair_inv_right
    (g : GaugeGroup 2) (v : FullL2 2) :
    actualOriginalFullL2GaugePairCLM g
      (actualOriginalFullL2GaugePairCLM g⁻¹ v) = v := by
  rw [actualOriginalFullL2GaugePair_mul,
    mul_inv_cancel, actualOriginalFullL2GaugePair_one]

/-- The original pairedGaugeData source map is a surjective
complex-linear Hilbert isometry, with inverse U(g⁻¹). -/
noncomputable def actualOriginalFullL2GaugeUnitaryEquiv
    (g : GaugeGroup 2) : FullL2 2 ≃ₗᵢ[ℂ] FullL2 2 where
  toLinearEquiv := {
    toFun := actualOriginalFullL2GaugePairCLM g
    invFun := actualOriginalFullL2GaugePairCLM g⁻¹
    left_inv := actualOriginalFullL2GaugePair_inv_left g
    right_inv := actualOriginalFullL2GaugePair_inv_right g
    map_add' := (actualOriginalFullL2GaugePairCLM g).map_add
    map_smul' := (actualOriginalFullL2GaugePairCLM g).map_smul
  }
  norm_map' := actualOriginalFullL2GaugePair_norm g

/-- The unitary equivalence is EXACTLY the original source
FullL2 operator from L6G7U, rather than a surrogate representation. -/
theorem actualOriginalFullL2GaugeUnitaryEquiv_apply
    (g : GaugeGroup 2) (v : FullL2 2) :
    actualOriginalFullL2GaugeUnitaryEquiv g v =
      actualOriginalFullL2GaugePairCLM g v := rfl

/-- Source-exact group homomorphism of actual BFSS FullL2
unitaries. Algebraic unitary representation only: parameter
strong continuity remains an open analytical obligation. -/
noncomputable def actualOriginalFullL2GaugeUnitaryHom :
    GaugeGroup 2 →* (FullL2 2 ≃ₗᵢ[ℂ] FullL2 2) where
  toFun := actualOriginalFullL2GaugeUnitaryEquiv
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro v
    change actualOriginalFullL2GaugePairCLM (1 : GaugeGroup 2) v = v
    exact actualOriginalFullL2GaugePair_one v
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro v
    change actualOriginalFullL2GaugePairCLM (g * h) v =
      actualOriginalFullL2GaugePairCLM g
        (actualOriginalFullL2GaugePairCLM h v)
    exact (actualOriginalFullL2GaugePair_mul g h v).symm

#print axioms actualOriginalFullL2GaugePair_inv_left
#print axioms actualOriginalFullL2GaugePair_inv_right
#print axioms actualOriginalFullL2GaugeUnitaryEquiv
#print axioms actualOriginalFullL2GaugeUnitaryEquiv_apply
#print axioms actualOriginalFullL2GaugeUnitaryHom
#check @actualOriginalFullL2GaugeUnitaryHom

end
end FCP.BFSSSU2PhysicalDomainL6G7Z
