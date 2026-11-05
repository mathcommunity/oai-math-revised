import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentPhysicalSpace

/-!
M4C3B — strict restricted Hilbert-space unitary candidate.

Construct the unitary equivalence of the independently defined SU(2)
gauge-constraint physical submodule and the LITERAL original
pairedGaugeData.physicalSpace. Uses accepted M4C3 Gate #2 membership
equivalence and M4C2 full-L2 unitary; no physical-space definition is
transported by fiat. No core, unbounded domain, or spectral assertion.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.IndependentPhysicalSpace
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentFullL2GaugeTransport
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

private abbrev μ := (volume : Measure (Boson 2))

variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
  theta α A * theta β B + theta β B * theta α A =
    (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
variable (hHermitian : ∀ α A, (theta α A).IsSymmetric)

/-- The literal restricted full-L2 equivalence with both inverses
witnessed by M4C3 physical-membership iff; no new gauge action. -/
def independentPhysicalLinearEquiv
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w)) :
    independentPhysicalSpace theta hCAR hHermitian ≃ₗ[ℂ]
      pairedGaugeData.physicalSpace where
  toFun v :=
    ⟨fiberTransportUnitary J v.val,
      (independentPhysicalSpace_iff_source theta hCAR hHermitian J hJ v.val).mp v.prop⟩
  invFun v :=
    ⟨(fiberTransportUnitary J).symm v.val,
      (independentPhysicalSpace_iff_source theta hCAR hHermitian J hJ
        ((fiberTransportUnitary J).symm v.val)).mpr
          (by
            have hright :
                (fiberTransportUnitary J) ((fiberTransportUnitary J).symm v.val) = v.val :=
              (fiberTransportUnitary J).apply_symm_apply v.val
            exact hright.symm ▸ v.prop)⟩
  left_inv := by
    intro v
    apply Subtype.ext
    exact (fiberTransportUnitary J).symm_apply_apply v.val
  right_inv := by
    intro v
    apply Subtype.ext
    exact (fiberTransportUnitary J).apply_symm_apply v.val
  map_add' := by
    intro v w
    apply Subtype.ext
    exact (fiberTransportUnitary J).map_add v.val w.val
  map_smul' := by
    intro c v
    apply Subtype.ext
    exact (fiberTransportUnitary J).map_smul c v.val

/-- Forward operator bound is the actual full-L2 fiberwise isometry. -/
theorem independentPhysicalLinearEquiv_norm_le
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (v : independentPhysicalSpace theta hCAR hHermitian) :
    ‖independentPhysicalLinearEquiv theta hCAR hHermitian J hJ v‖ ≤ ‖v‖ := by
  change ‖fiberTransportUnitary J (v : Lp E 2 μ)‖ ≤ ‖(v : Lp E 2 μ)‖
  exact le_of_eq ((fiberTransportUnitary J).norm_map (v : Lp E 2 μ))

/-- Inverse operator bound is the actual inverse full-L2 isometry. -/
theorem independentPhysicalLinearEquiv_symm_norm_le
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (v : pairedGaugeData.physicalSpace) :
    ‖(independentPhysicalLinearEquiv theta hCAR hHermitian J hJ).symm v‖ ≤ ‖v‖ := by
  change ‖(fiberTransportUnitary J).symm (v : FullL2 2)‖ ≤ ‖(v : FullL2 2)‖
  exact le_of_eq ((fiberTransportUnitary J).symm.norm_map (v : FullL2 2))

/-- Genuine complex-linear isometric equivalence between the independently
constructed physical SU2 gauge-constraint space and the literal original
BFSS physicalSpace. This remains conditional on the source-exact
generator-preserving unitary J, whose existence is available from M3J. -/
def independentPhysicalUnitary
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w)) :
    independentPhysicalSpace theta hCAR hHermitian ≃ₗᵢ[ℂ]
      pairedGaugeData.physicalSpace :=
  LinearIsometryEquiv.ofBounds
    (independentPhysicalLinearEquiv theta hCAR hHermitian J hJ)
    (independentPhysicalLinearEquiv_norm_le theta hCAR hHermitian J hJ)
    (by
      intro v
      exact independentPhysicalLinearEquiv_symm_norm_le theta hCAR hHermitian J hJ v)

#print axioms independentPhysicalLinearEquiv
#print axioms independentPhysicalLinearEquiv_norm_le
#print axioms independentPhysicalLinearEquiv_symm_norm_le
#print axioms independentPhysicalUnitary

end
end FCP.IndependentPhysicalSpace
