import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7XOriginalSourceFullL2FermionRepresentationProbe

/-!
L6G7Y — genuine ORIGINAL BFSS FullL2 finite SU(2) gauge
representation group law for the exact source pairedGaugeData.

Source GaugeCore chooses:
  B(g) f = bosonPullback g f = f ∘ (pairedGaugeData.boson g)
  F(g) f = fiberAction g f = pairedGaugeData.fermion g ∘ f
  U(g) := F(g) ∘ B(g⁻¹).

The original boson action itself is a group homomorphism;
its L² pullback is ANTIcontravariant B(g) B(h) = B(hg).
The source fiber action is covariant F(g)F(h)=F(gh) (L6G7X).
Because the source fermion gauge map acts on the fiber independent
of position, B(g)F(h)=F(h)B(g). Combining these without ANY sign or
order changes gives U(g)U(h)=U(gh), U(1)=id.

Only the genuine pinned GaugeCore FullL2 mappings and Mathlib Lp
measure-preserving almost-everywhere composition lemmas are used.
Strong parameter continuity, unbounded generator domain and
BFSS spectral statements remain separate OPEN obligations.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace FCP.BFSSSU2PhysicalDomainL6G7Y
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6G7X
open MeasureTheory

/-- Original source boson gauge pullback reverses multiplication.
The reversal is ESSENTIAL to the original physical-state convention. -/
theorem actualSourceFullL2_bosonPullback_anti_mul
    (g h : GaugeGroup 2) (v : FullL2 2) :
    pairedGaugeData.bosonPullback g
      (pairedGaugeData.bosonPullback h v) =
        pairedGaugeData.bosonPullback (h * g) v := by
  apply Lp.ext_iff.mpr
  have ho := Lp.coeFn_compMeasurePreserving
    (pairedGaugeData.bosonPullback h v)
    (pairedGaugeData.boson g).measurePreserving
  have hi := Lp.coeFn_compMeasurePreserving v
    (pairedGaugeData.boson h).measurePreserving
  have hinner := hi.comp_tendsto
    (pairedGaugeData.boson g).measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hp := Lp.coeFn_compMeasurePreserving v
    (pairedGaugeData.boson (h * g)).measurePreserving
  filter_upwards [ho, hinner, hp] with x houter hmid hprod
  calc
    _ = (pairedGaugeData.bosonPullback h v)
      (pairedGaugeData.boson g x) := by
        change (pairedGaugeData.bosonPullback g
            (pairedGaugeData.bosonPullback h v)) x =
          (pairedGaugeData.bosonPullback h v) (pairedGaugeData.boson g x)
          at houter
        exact houter
    _ = v (pairedGaugeData.boson h (pairedGaugeData.boson g x)) := by
        change (pairedGaugeData.bosonPullback h v)
            (pairedGaugeData.boson g x) =
          v (pairedGaugeData.boson h (pairedGaugeData.boson g x))
          at hmid
        exact hmid
    _ = v (pairedGaugeData.boson (h * g) x) := by
        rw [map_mul]
        rfl
    _ = (pairedGaugeData.bosonPullback (h * g) v) x := by
        change (pairedGaugeData.bosonPullback (h * g) v) x =
          v (pairedGaugeData.boson (h * g) x) at hprod
        exact hprod.symm

/-- The genuine original bosonic source pullback fixes the identity. -/
theorem actualSourceFullL2_bosonPullback_one
    (v : FullL2 2) :
    pairedGaugeData.bosonPullback (1 : GaugeGroup 2) v = v := by
  apply Lp.ext_iff.mpr
  have h := Lp.coeFn_compMeasurePreserving v
    (pairedGaugeData.boson (1 : GaugeGroup 2)).measurePreserving
  filter_upwards [h] with x hx
  calc
    (pairedGaugeData.bosonPullback (1 : GaugeGroup 2) v) x =
      v (pairedGaugeData.boson (1 : GaugeGroup 2) x) := by
        change (pairedGaugeData.bosonPullback (1 : GaugeGroup 2) v) x =
          v (pairedGaugeData.boson (1 : GaugeGroup 2) x) at hx
        exact hx
    _ = v x := by simp

/-- Original bosonic coordinate pullback and original Fock fiber
transformation commute on actual FullL2 using AE transport under
the genuine source measure-preserving boson gauge isometry. -/
theorem actualSourceFullL2_bosonPullback_fiber_comm
    (g h : GaugeGroup 2) (v : FullL2 2) :
    pairedGaugeData.bosonPullback g
      (pairedGaugeData.fiberAction h v) =
        pairedGaugeData.fiberAction h
          (pairedGaugeData.bosonPullback g v) := by
  apply Lp.ext_iff.mpr
  have hb := Lp.coeFn_compMeasurePreserving
    (pairedGaugeData.fiberAction h v)
    (pairedGaugeData.boson g).measurePreserving
  have hf := ContinuousLinearMap.coeFn_compLp
    (pairedGaugeData.fermion h).toContinuousLinearEquiv.toContinuousLinearMap v
  -- Gate #229: coeFn_compLp elaborates through the underlying
  -- measure-zero-set equality. Retype it as an EventuallyEq before
  -- applying the source boson gauge quasi-measure-preserving pullback.
  have hfAe :
      (fun a : Boson 2 => (pairedGaugeData.fiberAction h v) a) =ᵐ[volume]
        (fun a : Boson 2 => pairedGaugeData.fermion h (v a)) := by
    exact hf
  have hfc := hfAe.comp_tendsto
    (pairedGaugeData.boson g).measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hi := Lp.coeFn_compMeasurePreserving v
    (pairedGaugeData.boson g).measurePreserving
  have hp := ContinuousLinearMap.coeFn_compLp
    (pairedGaugeData.fermion h).toContinuousLinearEquiv.toContinuousLinearMap
      (pairedGaugeData.bosonPullback g v)
  filter_upwards [hb, hfc, hi, hp] with x hboson hfiber hinner hprod
  calc
    (pairedGaugeData.bosonPullback g
      (pairedGaugeData.fiberAction h v)) x =
        (pairedGaugeData.fiberAction h v)
          (pairedGaugeData.boson g x) := by
            change (pairedGaugeData.bosonPullback g
                (pairedGaugeData.fiberAction h v)) x =
              (pairedGaugeData.fiberAction h v) (pairedGaugeData.boson g x)
              at hboson
            exact hboson
    _ = pairedGaugeData.fermion h
          (v (pairedGaugeData.boson g x)) := by
            change (pairedGaugeData.fiberAction h v)
                (pairedGaugeData.boson g x) =
              pairedGaugeData.fermion h (v (pairedGaugeData.boson g x))
              at hfiber
            exact hfiber
    _ = pairedGaugeData.fermion h
          ((pairedGaugeData.bosonPullback g v) x) := by
            change (pairedGaugeData.bosonPullback g v) x =
              v (pairedGaugeData.boson g x) at hinner
            rw [hinner]
    _ = (pairedGaugeData.fiberAction h
          (pairedGaugeData.bosonPullback g v)) x := by
            change (pairedGaugeData.fiberAction h
                (pairedGaugeData.bosonPullback g v)) x =
              pairedGaugeData.fermion h
                ((pairedGaugeData.bosonPullback g v) x) at hprod
            exact hprod.symm

/-- Full original source-exact BFSS SU(2) group law on FullL2.
The inverse on the bosonic pullback is NOT optional. -/
theorem actualOriginalFullL2GaugePair_mul
    (g h : GaugeGroup 2) (v : FullL2 2) :
    actualOriginalFullL2GaugePairCLM g
      (actualOriginalFullL2GaugePairCLM h v) =
        actualOriginalFullL2GaugePairCLM (g * h) v := by
  change
    pairedGaugeData.fiberAction g
      (pairedGaugeData.bosonPullback g⁻¹
        (pairedGaugeData.fiberAction h
          (pairedGaugeData.bosonPullback h⁻¹ v))) =
    pairedGaugeData.fiberAction (g * h)
      (pairedGaugeData.bosonPullback (g * h)⁻¹ v)
  rw [actualSourceFullL2_bosonPullback_fiber_comm,
    actualSourceFullL2_fiberAction_mul,
    actualSourceFullL2_bosonPullback_anti_mul,
    mul_inv_rev]

/-- Source-exact original combined FullL2 SU(2) action at identity. -/
theorem actualOriginalFullL2GaugePair_one
    (v : FullL2 2) :
    actualOriginalFullL2GaugePairCLM (1 : GaugeGroup 2) v = v := by
  change pairedGaugeData.fiberAction (1 : GaugeGroup 2)
    (pairedGaugeData.bosonPullback (1 : GaugeGroup 2)⁻¹ v) = v
  rw [inv_one, actualSourceFullL2_bosonPullback_one,
    actualSourceFullL2_fiberAction_one]

#print axioms actualSourceFullL2_bosonPullback_anti_mul
#print axioms actualSourceFullL2_bosonPullback_one
#print axioms actualSourceFullL2_bosonPullback_fiber_comm
#print axioms actualOriginalFullL2GaugePair_mul
#print axioms actualOriginalFullL2GaugePair_one
#check @actualOriginalFullL2GaugePair_mul
#check @actualOriginalFullL2GaugePair_one

end
end FCP.BFSSSU2PhysicalDomainL6G7Y
