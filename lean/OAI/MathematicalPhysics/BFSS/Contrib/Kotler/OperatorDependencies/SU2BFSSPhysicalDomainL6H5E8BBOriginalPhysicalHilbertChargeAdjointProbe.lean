import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8BAOriginalPhysicalChargeUnconditionalDensityProbe
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# H5E8BB — genuine original physical Hilbert sixteen-charge adjoint

PROSPECTIVE / UNCOMPILED until strict pinned Actions kernel/axiom gate.

BA qualified UNCONDITIONAL density of the actual AY source-original minimal
charge operator on the true original gauge invariant physical Hilbert space.
The output is PiLp 2 of all sixteen original source FullL2 charges. Hence
Mathlib's genuine densely-defined Hilbert adjoint can be used, with NO
surrogate full-L2 domain or deformed-source graph identification.

This source constructs and verifies the actual Hilbert adjoint and its
original physical pairing and graph-closedness, NOT a Hamiltonian or the
manuscript's independent Clifford/Fock realization.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8BB
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open FCP.BFSSSU2PhysicalDomainL6H5E8BA
open Set
open scoped InnerProductSpace

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- Completeness is inherited from the actual source gauge-invariant
closed Hilbert subspace, not an invented extra assumption. -/
theorem originalPhysicalHilbertComplete :
    CompleteSpace G.physicalSpace :=
  (G.physicalSpace_closed).isComplete.completeSpace_coe

/-- The REAL Mathlib Hilbert adjoint of the genuine AY original
source sixteen-charge column, on its exact natural domain. -/
noncomputable def originalMinimalPhysicalHilbertChargeAdjoint :
    (PiLp 2 (fun _ : SpinIndex => FullL2 2)) →ₗ.[ℂ] G.physicalSpace := by
  letI : CompleteSpace G.physicalSpace := originalPhysicalHilbertComplete M G
  exact (originalMinimalPhysicalHilbertChargeColumn M G).adjoint

/-- The adjoint is the genuine formal Hilbert adjoint on the two
native partial-operator domains, using BA's newly proven density. -/
theorem originalMinimalPhysicalHilbertChargeAdjoint_isFormalAdjoint :
    (originalMinimalPhysicalHilbertChargeAdjoint M G).IsFormalAdjoint
      (originalMinimalPhysicalHilbertChargeColumn M G) := by
  letI : CompleteSpace G.physicalSpace := originalPhysicalHilbertComplete M G
  exact LinearPMap.adjoint_isFormalAdjoint
    (originalMinimalPhysicalHilbertChargeColumn_domain_dense_unconditional M G)

/-- The genuine Hilbert adjoint is closed on its exact native graph.
No claim about self-adjointness of the charge or of T†T is made. -/
theorem originalMinimalPhysicalHilbertChargeAdjoint_isClosed :
    (originalMinimalPhysicalHilbertChargeAdjoint M G).IsClosed := by
  letI : CompleteSpace G.physicalSpace := originalPhysicalHilbertComplete M G
  exact LinearPMap.adjoint_isClosed
    (originalMinimalPhysicalHilbertChargeColumn_domain_dense_unconditional M G)

/-- The exact original 16-charge Hilbert pairing, without changing
the original gamma, SU(2) gauge representation or source operator. -/
theorem originalMinimalPhysicalHilbertChargeAdjoint_inner
    (u : (originalMinimalPhysicalHilbertChargeColumn M G).domain)
    (v : (originalMinimalPhysicalHilbertChargeAdjoint M G).domain) :
    inner ℂ (originalMinimalPhysicalHilbertChargeAdjoint M G v)
      (u : G.physicalSpace) =
    inner ℂ (v : PiLp 2 (fun _ : SpinIndex => FullL2 2))
      (originalMinimalPhysicalHilbertChargeColumn M G u) := by
  exact (originalMinimalPhysicalHilbertChargeAdjoint_isFormalAdjoint M G) v u

#print axioms originalPhysicalHilbertComplete
#print axioms originalMinimalPhysicalHilbertChargeAdjoint
#print axioms originalMinimalPhysicalHilbertChargeAdjoint_isFormalAdjoint
#print axioms originalMinimalPhysicalHilbertChargeAdjoint_isClosed
#print axioms originalMinimalPhysicalHilbertChargeAdjoint_inner

end
end FCP.BFSSSU2PhysicalDomainL6H5E8BB
