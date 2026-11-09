import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5C3OriginalGaussCandidatePointwiseDerivativeBridgeProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7BOriginalPlusIGaugeCurveGroupLawProbe

/-!
L6H5D1 — the exact ORIGINAL source SmoothCore gauge orbit has a
pointwise representation composition law, including the mandatory
inverse bosonic pullback. Specialize this to the original +i source
color curve. This is the first leaf toward transporting the
H5C3 time-zero Gauss derivative to arbitrary real time.

No pointwise differentiability at nonzero times, FullL2 norm
differentiability, generator-domain or BFSS spectral claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5D1
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6H0
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7B

/-!
Gate #273: all preceding source checks passed; this new leaf failed
at a terminal `rfl` with maximum recursion depth (not a source-sign
counterexample). Do NOT re-elaborate the large concrete pairedGaugeData
in the final definitional equality. Prove the generic monoid-hom
identity first, then specialize it to the exact qualified source.
-/

/-- Pure group-action composition with distinct boson and fermion
monoid homomorphisms. No concrete Fock implementation elaboration. -/
private theorem pointwisePairOrbit_mul_abstract
    (B : GaugeGroup 2 →* (Boson 2 ≃ₗᵢ[ℝ] Boson 2))
    (F : GaugeGroup 2 →* (Fermion 2 ≃ₗᵢ[ℂ] Fermion 2))
    (u : Boson 2 → Fermion 2)
    (g h : GaugeGroup 2) (x : Boson 2) :
    F (g * h) (u (B (g * h)⁻¹ x)) =
      F g (F h (u (B h⁻¹ (B g⁻¹ x)))) := by
  rw [mul_inv_rev, map_mul F g h, map_mul B h⁻¹ g⁻¹]
  rfl

/-- Original gauge action on the literal source SmoothCore is
covariant: fermion(g*h) and boson((g*h)^(-1)) retain their
original ordering and are never replaced by surrogate actions. -/
theorem actualOriginalSmoothGaugeOrbit_pointwise_mul
    (f : SmoothCore 2) (g h : GaugeGroup 2) (x : Boson 2) :
    actualOriginalSmoothGaugeOrbitRepresentative f (g * h) x =
      pairedGaugeData.fermion g
        (actualOriginalSmoothGaugeOrbitRepresentative f h
          (pairedGaugeData.boson g⁻¹ x)) := by
  change pairedGaugeData.fermion (g * h)
    (f (pairedGaugeData.boson (g * h)⁻¹ x)) =
    pairedGaugeData.fermion g
      (pairedGaugeData.fermion h
        (f (pairedGaugeData.boson h⁻¹
          (pairedGaugeData.boson g⁻¹ x))))
  -- Source representation identity is proved for opaque homomorphisms,
  -- then instantiated once; avoid concrete six-field GaugeData reduction.
  exact pointwisePairOrbit_mul_abstract
    pairedGaugeData.boson pairedGaugeData.fermion f g h x

/-- Specialization to the exact +i native one-parameter SU2 group,
not a newly defined gauge action. -/
theorem actualOriginalSmoothGaugeOrbit_colorCurve_add
    (c : ColorIndex 2) (f : SmoothCore 2) (s t : ℝ)
    (x : Boson 2) :
    actualOriginalSmoothGaugeOrbitRepresentative f
      (sourcePlusIGaugeCurve c (s + t)) x =
    pairedGaugeData.fermion (sourcePlusIGaugeCurve c s)
      (actualOriginalSmoothGaugeOrbitRepresentative f
        (sourcePlusIGaugeCurve c t)
          (pairedGaugeData.boson
            (sourcePlusIGaugeCurve c s)⁻¹ x)) := by
  rw [sourcePlusIGaugeCurve_add]
  exact actualOriginalSmoothGaugeOrbit_pointwise_mul f
    (sourcePlusIGaugeCurve c s) (sourcePlusIGaugeCurve c t) x

#print axioms actualOriginalSmoothGaugeOrbit_pointwise_mul
#print axioms actualOriginalSmoothGaugeOrbit_colorCurve_add
#check @actualOriginalSmoothGaugeOrbit_pointwise_mul
#check @actualOriginalSmoothGaugeOrbit_colorCurve_add

end
end FCP.BFSSSU2PhysicalDomainL6H5D1
