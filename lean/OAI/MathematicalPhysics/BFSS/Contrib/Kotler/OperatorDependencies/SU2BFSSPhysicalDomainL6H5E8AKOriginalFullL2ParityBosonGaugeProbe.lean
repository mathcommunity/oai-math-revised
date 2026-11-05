import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AIOriginalFullL2ParityLiftProbe
import OAI.MathematicalPhysics.BFSS.GaugeCore

/-!
# H5E8AK — original FullL2 parity commutes with literal source SU2 bosonic gauge pullback

This tests a required physical-domain step, not a separate
SU2 implementation. Uses the original GaugeData.boson : GaugeGroup N
→* (Boson N ≃ₗᵢ[ℝ] Boson N), hence its actual linearity under -x.
The exact source GaugeData.bosonPullback is a Mathlib Lp
measure-preserving composition; apply the already accepted AI parity
and Mathlib Lp.compMeasurePreserving_comp_apply to commute them.

PROSPECTIVE only; no new mathematical axiom, no statement about
fermionic source fiberAction or complete physicalSpace yet.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AK
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AI
open MeasureTheory

/-- Literal original SU2 boson gauge action respects spatial
inversion, because it is a real-linear isometry equivalence. -/
theorem originalSourceGaugeBoson_commutes_neg {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (g : GaugeGroup N) (x : Boson N) :
    G.boson g (-x) = -(G.boson g x) := by
  exact map_neg (G.boson g) x

/-- On the exact original FullL2 N, spatial parity commutes
with G.bosonPullback g for every original SU2 gauge group element.
No pointwise representatives are postulated: this is equality of
the two actual complex-linear Lp pullback operators. -/
theorem originalFullL2Parity_bosonPullback {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) (g : GaugeGroup N)
    (v : FullL2 N) :
    originalFullL2Parity (G.bosonPullback g v) =
      G.bosonPullback g (originalFullL2Parity v) := by
  let inv : Boson N → Boson N := fun x => -x
  let hi : MeasurePreserving inv
      (volume : Measure (Boson N)) (volume : Measure (Boson N)) :=
    originalBosonNeg_measurePreserving
  let hg := (G.boson g).measurePreserving
  change Lp.compMeasurePreserving inv hi
      (Lp.compMeasurePreserving (G.boson g) hg v) =
    Lp.compMeasurePreserving (G.boson g) hg
      (Lp.compMeasurePreserving inv hi v)
  have hcomm : (G.boson g : Boson N → Boson N) ∘ inv =
      inv ∘ (G.boson g : Boson N → Boson N) := by
    funext x
    exact originalSourceGaugeBoson_commutes_neg M G g x
  calc
    Lp.compMeasurePreserving inv hi
        (Lp.compMeasurePreserving (G.boson g) hg v) =
      Lp.compMeasurePreserving
        ((G.boson g : Boson N → Boson N) ∘ inv)
        (hg.comp hi) v :=
      (Lp.compMeasurePreserving_comp_apply v hg hi).symm
    _ = Lp.compMeasurePreserving
        (inv ∘ (G.boson g : Boson N → Boson N))
        (hi.comp hg) v := by
      -- Avoid rewriting the domain map underneath its dependently typed
      -- MeasurePreserving certificate; compare genuine Lp representatives.
      apply Lp.ext
      have hleft := Lp.coeFn_compMeasurePreserving v (hg.comp hi)
      have hright := Lp.coeFn_compMeasurePreserving v (hi.comp hg)
      filter_upwards [hleft, hright] with x hl hr
      calc
        (Lp.compMeasurePreserving
            ((G.boson g : Boson N → Boson N) ∘ inv)
            (hg.comp hi) v) x =
          v (((G.boson g : Boson N → Boson N) ∘ inv) x) := hl
        _ = v ((inv ∘ (G.boson g : Boson N → Boson N)) x) := by
          rw [hcomm]
        _ = (Lp.compMeasurePreserving
            (inv ∘ (G.boson g : Boson N → Boson N))
            (hi.comp hg) v) x := hr.symm
    _ = Lp.compMeasurePreserving (G.boson g) hg
        (Lp.compMeasurePreserving inv hi v) :=
      Lp.compMeasurePreserving_comp_apply v hi hg

#print axioms originalSourceGaugeBoson_commutes_neg
#print axioms originalFullL2Parity_bosonPullback

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AK
