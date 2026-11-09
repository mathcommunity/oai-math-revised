import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1BRelativeGaugeImplementerProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4BFermionLinearTransportProbe

/-!
# S1D: Scalar ambiguity is a genuine group character for an alternative
# 48-theta covariant SU2 gauge implementer on the SOURCE Fock representation.

PROSPECTIVE — not accepted until source-pinned strict Lean compilation and
complete axiom audit. This theorem neither constructs the independent
manuscript's Clifford module/intertwiner nor assumes its Spin(48) lift.

Given a *second* group homomorphism V of invertible complex-linear source
Fock maps which satisfies the actual accepted 48-theta color covariance,
S1B's Schur argument supplies a unique complex scalar χ(g) such that
V(g)=χ(g) fermionGaugeLinearEquiv(g). This module tests χ(1)=1,
χ(gh)=χ(g)χ(h) and χ(g) ≠ 0 on the actual nonzero 2^24-dimensional
source module. Triviality of all SU2→ℂˣ characters, continuity,
and existence of an independent paper Spin(48) lift are separate burdens.
-/

set_option autoImplicit false
set_option maxHeartbeats 180000

namespace FCP.BFSSSU2PhysicalDomainS1D
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4B
open FCP.BFSSSU2PhysicalDomainS1B

variable (V : GaugeGroup 2 →* (Fermion 2 ≃ₗ[ℂ] Fermion 2))
variable (hV : ∀ (g : GaugeGroup 2) (α : SpinIndex)
  (A : ColorIndex 2) (v : Fermion 2),
  V g (pairedTheta α A v) =
    ∑ B : ColorIndex 2,
      (pairedAlgebraData.adjointCoefficient g A B : ℂ) •
        pairedTheta α B (V g v))

/-- The unique relative scalar is selected from S1B's proven
same-covariance Schur conclusion, rather than assumed. -/
noncomputable def relativeGaugeScalar (g : GaugeGroup 2) : ℂ :=
  Classical.choose (theta_covariant_implementer_scalar g
    (V g) (hV g))

theorem relativeGaugeScalar_apply (g : GaugeGroup 2) (v : Fermion 2) :
    V g v = relativeGaugeScalar V hV g • fermionGaugeLinearEquiv g v :=
  Classical.choose_spec (theta_covariant_implementer_scalar g
    (V g) (hV g)) v

/-- A nonzero vector on the literal source Fock Hilbert type suffices
to eliminate any freedom in the scalar of a fixed invertible gauge map. -/
private theorem relativeScalar_unique
    (g : GaugeGroup 2) (a b : ℂ)
    (ha : ∀ v : Fermion 2, V g v = a • fermionGaugeLinearEquiv g v)
    (hb : ∀ v : Fermion 2, V g v = b • fermionGaugeLinearEquiv g v) :
    a = b := by
  obtain ⟨v, hv⟩ : ∃ v : Fermion 2, v ≠ 0 := exists_ne 0
  have hw : fermionGaugeLinearEquiv g v ≠ 0 := by
    intro hh
    apply hv
    apply (fermionGaugeLinearEquiv g).injective
    simpa only [map_zero] using hh
  have heq : a • fermionGaugeLinearEquiv g v =
      b • fermionGaugeLinearEquiv g v := (ha v).symm.trans (hb v)
  have hdiff : (a-b) • fermionGaugeLinearEquiv g v = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact heq
  rcases smul_eq_zero.mp hdiff with h0 | hz
  · exact sub_eq_zero.mp h0
  · exact (hw hz).elim

theorem relativeGaugeScalar_one :
    relativeGaugeScalar V hV 1 = 1 := by
  apply relativeScalar_unique V (1 : GaugeGroup 2)
  · exact relativeGaugeScalar_apply V hV 1
  · intro v
    change (V 1) v = (1 : ℂ) • (fermionGaugeLinearHom 1) v
    rw [map_one V, map_one fermionGaugeLinearHom]
    simp

theorem relativeGaugeScalar_mul (g h : GaugeGroup 2) :
    relativeGaugeScalar V hV (g*h) =
      relativeGaugeScalar V hV g * relativeGaugeScalar V hV h := by
  apply relativeScalar_unique V (g*h)
  · exact relativeGaugeScalar_apply V hV (g*h)
  · intro v
    have hfgh :
        fermionGaugeLinearEquiv (g*h) v =
        fermionGaugeLinearEquiv g (fermionGaugeLinearEquiv h v) := by
      change (fermionGaugeLinearHom (g*h)) v =
        (fermionGaugeLinearHom g) ((fermionGaugeLinearHom h) v)
      rw [map_mul]
      rfl
    calc
      V (g*h) v = V g (V h v) := by
        rw [map_mul V, LinearEquiv.mul_apply]
      _ = V g (relativeGaugeScalar V hV h •
          fermionGaugeLinearEquiv h v) := by
          rw [relativeGaugeScalar_apply V hV h]
      _ = relativeGaugeScalar V hV h •
          V g (fermionGaugeLinearEquiv h v) := map_smul _ _ _
      _ = relativeGaugeScalar V hV h •
          (relativeGaugeScalar V hV g •
            fermionGaugeLinearEquiv g (fermionGaugeLinearEquiv h v)) := by
            rw [relativeGaugeScalar_apply V hV g]
      _ = (relativeGaugeScalar V hV g * relativeGaugeScalar V hV h) •
          fermionGaugeLinearEquiv (g*h) v := by
            rw [hfgh, smul_smul,
              mul_comm (relativeGaugeScalar V hV h)
                (relativeGaugeScalar V hV g)]

theorem relativeGaugeScalar_ne_zero (g : GaugeGroup 2) :
    relativeGaugeScalar V hV g ≠ 0 := by
  intro hz
  obtain ⟨v, hv⟩ : ∃ v : Fermion 2, v ≠ 0 := exists_ne 0
  have hzero : V g v = 0 := by
    rw [relativeGaugeScalar_apply V hV g, hz, zero_smul]
  apply hv
  apply (V g).injective
  simpa only [map_zero] using hzero

#print axioms relativeGaugeScalar
#print axioms relativeGaugeScalar_apply
#print axioms relativeGaugeScalar_one
#print axioms relativeGaugeScalar_mul
#print axioms relativeGaugeScalar_ne_zero

end
end FCP.BFSSSU2PhysicalDomainS1D
