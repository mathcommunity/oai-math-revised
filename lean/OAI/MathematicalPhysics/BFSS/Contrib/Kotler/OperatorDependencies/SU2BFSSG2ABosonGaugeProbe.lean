import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG1BColorAnnihilatorProbe
import OAI.MathematicalPhysics.BFSS.GaugeCore

/-!
# BFSS SU(2) G2-A — actual bosonic gauge group action and adjoint covariance

For the accepted pairedAlgebraData : AlgebraData 2, construct the
genuine GaugeGroup 2 →* (Boson 2 ≃ₗᵢ[ℝ] Boson 2) action, and the
exact upstream boson_adjoint identity.

The fermionic representation, both continuity fields and the complete
AlgebraData.GaugeData are NOT constructed in this gate.
-/

namespace FCP.BFSSSU2GaugeG2A
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A

private abbrev M : AlgebraData 2 := pairedAlgebraData

/-- The pinned conjugation action is a *real linear isometry equivalence*
on the actual twenty-seven-dimensional bosonic configuration space. -/
noncomputable def bosonGaugeEquiv (g : GaugeGroup 2) :
    Boson 2 ≃ₗᵢ[ℝ] Boson 2 where
  toLinearEquiv := {
    toFun := fun x => M.gaugeConjugate (g : ColorMatrix 2) x
    invFun := fun x => M.gaugeConjugate ((g⁻¹ : GaugeGroup 2) : ColorMatrix 2) x
    left_inv := by
      intro x
      calc
        M.gaugeConjugate ((g⁻¹ : GaugeGroup 2) : ColorMatrix 2)
            (M.gaugeConjugate (g : ColorMatrix 2) x) =
          M.gaugeConjugate (((g⁻¹ * g : GaugeGroup 2) : ColorMatrix 2)) x := by
            exact (M.gaugeConjugate_mul
              ((g⁻¹ : GaugeGroup 2) : ColorMatrix 2)
              (g : ColorMatrix 2) g.prop.1 x).symm
        _ = x := by
          rw [inv_mul_cancel]
          exact M.gaugeConjugate_one x
    right_inv := by
      intro x
      calc
        M.gaugeConjugate (g : ColorMatrix 2)
            (M.gaugeConjugate ((g⁻¹ : GaugeGroup 2) : ColorMatrix 2) x) =
          M.gaugeConjugate (((g * g⁻¹ : GaugeGroup 2) : ColorMatrix 2)) x := by
            exact (M.gaugeConjugate_mul
              (g : ColorMatrix 2)
              ((g⁻¹ : GaugeGroup 2) : ColorMatrix 2)
              (g⁻¹).prop.1 x).symm
        _ = x := by
          rw [mul_inv_cancel]
          exact M.gaugeConjugate_one x
    map_add' := by
      intro x y
      obtain ⟨L, hL⟩ := M.gaugeConjugate_linear (g : ColorMatrix 2)
      simpa only [hL] using L.map_add x y
    map_smul' := by
      intro c x
      obtain ⟨L, hL⟩ := M.gaugeConjugate_linear (g : ColorMatrix 2)
      simpa only [RingHom.id_apply, hL] using L.map_smul c x
  }
  norm_map' := by
    intro x
    have hinner := M.gaugeConjugate_inner (g : ColorMatrix 2) g.prop.1 x x
    have hsq :
        ‖M.gaugeConjugate (g : ColorMatrix 2) x‖ ^ 2 = ‖x‖ ^ 2 := by
      calc
        _ = inner ℝ (M.gaugeConjugate (g : ColorMatrix 2) x)
              (M.gaugeConjugate (g : ColorMatrix 2) x) :=
          (real_inner_self_eq_norm_sq _).symm
        _ = inner ℝ x x := hinner
        _ = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq _
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The action is definitionally the genuine upstream gaugeConjugate. -/
theorem bosonGaugeEquiv_apply (g : GaugeGroup 2) (x : Boson 2) :
    bosonGaugeEquiv g x = M.gaugeConjugate (g : ColorMatrix 2) x := rfl

/-- The exact group representation required as the `boson` field of
the *upstream* AlgebraData.GaugeData structure (no GaugeData claimed). -/
noncomputable def bosonGauge :
    GaugeGroup 2 →* (Boson 2 ≃ₗᵢ[ℝ] Boson 2) where
  toFun := bosonGaugeEquiv
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    change M.gaugeConjugate (1 : ColorMatrix 2) x = x
    exact M.gaugeConjugate_one x
  map_mul' := by
    intro g h
    apply LinearIsometryEquiv.ext
    intro x
    change M.gaugeConjugate (((g * h : GaugeGroup 2) : ColorMatrix 2)) x =
      M.gaugeConjugate (g : ColorMatrix 2)
        (M.gaugeConjugate (h : ColorMatrix 2) x)
    exact M.gaugeConjugate_mul (g : ColorMatrix 2)
      (h : ColorMatrix 2) h.prop.1 x

/-- Prove the exact literal pinned boson_adjoint field for the paired
AlgebraData 2 witness, using the true special unitary matrix g. -/
theorem bosonGauge_adjoint (g : GaugeGroup 2) (x : Boson 2) (i : SpaceIndex) :
    M.matrixCoordinate (bosonGauge g x) i =
      (g : ColorMatrix 2) * M.matrixCoordinate x i *
        (g : ColorMatrix 2).conjTranspose := by
  change M.colorEmbed (spatialColor (M.gaugeConjugate (g : ColorMatrix 2) x) i) =
    (g : ColorMatrix 2) * M.colorEmbed (spatialColor x i) *
      (g : ColorMatrix 2).conjTranspose
  rw [M.spatialColor_gaugeConjugate]
  exact M.colorEmbed_conjugate (g : ColorMatrix 2) g.prop.1 (spatialColor x i)

/-- Interface summary: the first and third field of an eventual full
GaugeData can be given by these objects, without assuming other fields. -/
theorem bosonGauge_exact_fields :
    (∀ g x i, M.matrixCoordinate (bosonGauge g x) i =
      (g : ColorMatrix 2) * M.matrixCoordinate x i *
        (g : ColorMatrix 2).conjTranspose) :=
  bosonGauge_adjoint

#print axioms bosonGaugeEquiv
#print axioms bosonGaugeEquiv_apply
#print axioms bosonGauge
#print axioms bosonGauge_adjoint
#print axioms bosonGauge_exact_fields

end
end FCP.BFSSSU2GaugeG2A
