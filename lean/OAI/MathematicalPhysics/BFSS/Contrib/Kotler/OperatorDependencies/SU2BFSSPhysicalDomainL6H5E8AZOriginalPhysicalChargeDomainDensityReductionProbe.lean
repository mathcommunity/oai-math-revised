import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AYOriginalPhysicalHilbertChargeGraphProbe
import OAI.MathematicalPhysics.BFSS.ClosedProfiles

/-!
# H5E8AZ — physical operator domain density REDUCTION to invariant core

QUALIFICATION PENDING STRICT LEAN. This module does NOT invent or assume
an unconditional source density theorem. It proves a CONDITIONAL but
source-typed implication: IF the original source invariant SmoothCore
is dense in the genuine physical Hilbert G.physicalSpace, THEN the
actual original minimal closed physical input / PiLp-two output charge
operator constructed in qualified AY has DENSE NATURAL DOMAIN.

This is an exactly named interface for the historically accepted
D2B10C source Haar theorem at N=2:
  sourceCoreNormClosure_eq_physical_unconditional
which was source reviewed with passing original Gate #47.

The historical Haar theorem is NOT imported by this module: its cache
is not known reachable from current S3L PR. A separate reproducible,
pin-matched joint Gate is required to discharge the displayed premise
and claim UNCONDITIONAL density, adjoint or Hamiltonian properties.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AZ
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AU
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open MeasureTheory Set
open scoped InnerProductSpace

/-- Source original gauge-invariant SmoothCore vectors are included in
the ACTUAL physical-Hilbert operator's natural domain. No source
density or global spectral condition is assumed. -/
theorem originalMinimalPhysicalHilbertChargeColumn_core_mem_domain {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) (f : G.invariantCore) :
    ((⟨coreToL2 f.val, f.property⟩ : G.physicalSpace) :
      G.physicalSpace) ∈
      (originalMinimalPhysicalHilbertChargeColumn M G).domain := by
  let u : G.physicalSpace := ⟨coreToL2 f.val, f.property⟩
  have hcore :
      (coreToL2 f.val, M.chargeVector f.val) ∈
        originalMinimalCoreGraph M G := ⟨f,rfl⟩
  have hclosed :
      (coreToL2 f.val, M.chargeVector f.val) ∈
        originalMinimalClosedGraph M G := by
    change (coreToL2 f.val, M.chargeVector f.val) ∈
      closure (originalMinimalCoreGraph M G :
        Set (FullL2 N × (SpinIndex → FullL2 N)))
    exact subset_closure hcore
  have hphysical :
      (u, WithLp.toLp 2 (M.chargeVector f.val)) ∈
        originalMinimalPhysicalHilbertChargeGraph M G := by
    apply (originalMinimalPhysicalHilbertChargeGraph_mem_iff M G _).mpr
    change (coreToL2 f.val, M.chargeVector f.val) ∈
      originalMinimalClosedGraph M G
    exact hclosed
  have hgraph :
      (u, WithLp.toLp 2 (M.chargeVector f.val)) ∈
        (originalMinimalPhysicalHilbertChargeColumn M G).graph := by
    rw [originalMinimalPhysicalHilbertChargeColumn_graph_eq M G]
    exact hphysical
  exact LinearPMap.mem_domain_of_mem_graph hgraph

/-- Completely explicit reduction of PHYSICAL operator-domain density
to the original source invariant SmoothCore physical-space norm
closure. This does NOT assert the displayed hypothesis unconditionally.
Use the proven original D2B10C Haar theorem in a future jointly
qualified gate to discharge it without any new axiom. -/
theorem originalMinimalPhysicalHilbertChargeColumn_domain_dense_of_coreNormClosure_eq
    {N : ℕ} (M : AlgebraData N) (G : M.GaugeData)
    (hd : G.coreNormClosure = G.physicalSpace) :
    Dense ((originalMinimalPhysicalHilbertChargeColumn M G).domain :
      Set G.physicalSpace) := by
  rw [Subtype.dense_iff]
  have hs :
      (LinearMap.range (coreToL2.comp G.invariantCore.subtype) :
        Set (FullL2 N)) ⊆
      ((↑) '' ((originalMinimalPhysicalHilbertChargeColumn M G).domain :
        Set G.physicalSpace) : Set (FullL2 N)) := by
    rintro ψ ⟨f,rfl⟩
    let u : G.physicalSpace := ⟨coreToL2 f.val, f.property⟩
    refine ⟨u, ?_, rfl⟩
    exact originalMinimalPhysicalHilbertChargeColumn_core_mem_domain M G f
  calc
    (G.physicalSpace : Set (FullL2 N)) =
        (G.coreNormClosure : Set (FullL2 N)) :=
      congrArg (fun S : Submodule ℂ (FullL2 N) =>
        (S : Set (FullL2 N))) hd.symm
    _ = closure (LinearMap.range
        (coreToL2.comp G.invariantCore.subtype) : Set (FullL2 N)) := rfl
    _ ⊆ closure ((↑) '' ((originalMinimalPhysicalHilbertChargeColumn
        M G).domain : Set G.physicalSpace) : Set (FullL2 N)) :=
      closure_mono hs

#print axioms originalMinimalPhysicalHilbertChargeColumn_core_mem_domain
#print axioms originalMinimalPhysicalHilbertChargeColumn_domain_dense_of_coreNormClosure_eq

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AZ
