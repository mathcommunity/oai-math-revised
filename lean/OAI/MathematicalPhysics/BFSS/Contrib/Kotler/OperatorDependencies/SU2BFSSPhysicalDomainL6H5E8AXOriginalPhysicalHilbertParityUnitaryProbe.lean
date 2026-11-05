import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8ALOriginalFullL2PhysicalParityProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8ANOriginalOppositeGammaGaugeDataProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AJOriginalFullL2ParityUnitaryProbe
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# H5E8AX — genuine physical SU2 Hilbert input parity unitary

The accepted original AL source theorem says parity preserves the
literal gauge-invariant G.physicalSpace. The AJ source parity is a true
complex-linear isometry equivalence on FullL2. The pinned Mathlib
LinearIsometryEquiv.submoduleMap and .ofEq provide a genuine restricted
complex Hilbert unitary between physical SU2 subspaces.

For oppositeGamma M, the AN source reconstruction proves the exact
physical Hilbert subspace is the same. The result is a Hilbert unitary
on REAL physical input spaces, not merely FullL2 nor a formal equality
of gauge actions. This is needed for later true physical adjoint and
Hamiltonian operator-domain conjugation, which remain separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 240000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AX
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AI
open FCP.BFSSSU2PhysicalDomainL6H5E8AJ
open FCP.BFSSSU2PhysicalDomainL6H5E8AL
open FCP.BFSSSU2PhysicalDomainL6H5E8AN

/-- The *true* source gauge physical Hilbert submodule maps exactly
onto itself under source original spatial parity, in BOTH directions. -/
theorem originalPhysicalSpace_parity_image_eq {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    G.physicalSpace.map
        (originalFullL2ParityUnitary (N := N)).toLinearMap =
      G.physicalSpace := by
  apply le_antisymm
  · rintro v ⟨u, hu, rfl⟩
    exact originalFullL2Parity_mem_physicalSpace M G hu
  · intro v hv
    refine ⟨originalFullL2Parity v,
      originalFullL2Parity_mem_physicalSpace M G hv, ?_⟩
    exact originalFullL2Parity_involutive v

/-- A TRUE complex-linear isometric Hilbert equivalence on the
actual original gauge-invariant physical Hilbert input, not ambient
unrestricted FullL2 and not an assumed abstract gauge intertwiner. -/
noncomputable def originalPhysicalSpaceParityUnitary {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    G.physicalSpace ≃ₗᵢ[ℂ] G.physicalSpace :=
  ((originalFullL2ParityUnitary (N := N)).submoduleMap G.physicalSpace).trans
    (LinearIsometryEquiv.ofEq _ _
      (originalPhysicalSpace_parity_image_eq M G))

/-- Actual original physical input unitary is literally FullL2 spatial
parity on underlying source Hilbert vectors. -/
theorem originalPhysicalSpaceParityUnitary_apply {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (u : G.physicalSpace) :
    ((originalPhysicalSpaceParityUnitary M G u : G.physicalSpace) :
      FullL2 N) = originalFullL2Parity (u : FullL2 N) := by
  rfl

/-- It is genuinely involutive ON THE SOURCE PHYSICAL HILBERT SPACE. -/
theorem originalPhysicalSpaceParityUnitary_twice {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (u : G.physicalSpace) :
    originalPhysicalSpaceParityUnitary M G
      (originalPhysicalSpaceParityUnitary M G u) = u := by
  apply Subtype.ext
  change originalFullL2Parity (originalFullL2Parity (u : FullL2 N)) =
    (u : FullL2 N)
  exact originalFullL2Parity_involutive (u : FullL2 N)

/-- The genuine physical input Hilbert inner product is preserved,
providing the input half of the closed form Hamiltonian bridge. -/
theorem originalPhysicalSpaceParityUnitary_inner {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (u v : G.physicalSpace) :
    inner ℂ (originalPhysicalSpaceParityUnitary M G u)
      (originalPhysicalSpaceParityUnitary M G v) =
    inner ℂ u v := by
  exact (originalPhysicalSpaceParityUnitary M G).inner_map_map u v

/-- Valid source opposite-gamma GaugeData has the very SAME physical
gauge Hilbert space, so parity also yields a real two-model unitary. -/
noncomputable def originalOppositeGammaPhysicalParityUnitary {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    G.physicalSpace ≃ₗᵢ[ℂ]
      (originalOppositeGammaGaugeData M G).physicalSpace :=
  (originalPhysicalSpaceParityUnitary M G).trans
    (LinearIsometryEquiv.ofEq _ _
      (originalOppositeGammaGaugeData_physicalSpace M G).symm)

/-- Opposite-gamma unitary is literal original spatial parity on
the concrete FULL-L² representatives of gauge-invariant states. -/
theorem originalOppositeGammaPhysicalParityUnitary_apply {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) (u : G.physicalSpace) :
    ((originalOppositeGammaPhysicalParityUnitary M G u :
      (originalOppositeGammaGaugeData M G).physicalSpace) :
      FullL2 N) = originalFullL2Parity (u : FullL2 N) := by
  rfl

#print axioms originalPhysicalSpace_parity_image_eq
#print axioms originalPhysicalSpaceParityUnitary
#print axioms originalPhysicalSpaceParityUnitary_apply
#print axioms originalPhysicalSpaceParityUnitary_twice
#print axioms originalPhysicalSpaceParityUnitary_inner
#print axioms originalOppositeGammaPhysicalParityUnitary
#print axioms originalOppositeGammaPhysicalParityUnitary_apply

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AX
