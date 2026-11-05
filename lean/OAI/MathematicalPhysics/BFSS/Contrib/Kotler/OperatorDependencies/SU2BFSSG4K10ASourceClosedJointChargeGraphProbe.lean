import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K9DSourcePotentialMultiplierProbe
import OAI.MathematicalPhysics.BFSS.ClosedProfiles

/-!
# BFSS SU(2) G4-K10A — exact original closed joint-charge graph identity

UNCOMPILED candidate until an independently reported pinned CI gate is green.

This is a bounded source-typed corollary of the kernel-qualified G4-K9D
all-SmoothCore charge identity. It identifies exactly the joint graph closure
the upstream source defines; it does NOT identify the self-adjoint Hamiltonian,
its closed quadratic form or gauge-invariant physical operator domain.
-/

namespace FCP.BFSSSU2GaugeG4K10A
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG4K9D

/-- The deformed source's actual SmoothCore linear map equals the original
charge linear map at (h,m)=(1,0); no surrogate operator is introduced. -/
theorem sourceChargeMap_equal
    {N : ℕ} (M : AlgebraData N) (α : SpinIndex) :
    M.deformedChargeMap 1 0 α = M.charge α := by
  apply LinearMap.ext
  intro f
  exact sourceUnconditionalCoreCharge_equal M α f

/-- The exact source-defined joint L2 charge-vector linear maps coincide
for all smooth compactly supported sections, by componentwise equality. -/
theorem sourceChargeVector_equal
    {N : ℕ} (M : AlgebraData N) :
    M.deformedChargeVector 1 0 = M.chargeVector := by
  apply LinearMap.ext
  intro f
  funext α
  change coreToL2 (M.deformedChargeMap 1 0 α f) =
    coreToL2 (M.charge α f)
  rw [sourceChargeMap_equal M α]

/-- Equality of the genuine original smooth joint-charge graphs as submodules
in the SAME ambient L2 × (SpinIndex → L2) Hilbert space. -/
theorem sourceCoreGraph_equal
    {N : ℕ} (M : AlgebraData N) :
    M.deformedCoreGraph 1 0 = M.fullCoreGraph := by
  change LinearMap.range (coreToL2.prod (M.deformedChargeVector 1 0)) =
    LinearMap.range (coreToL2.prod M.chargeVector)
  rw [sourceChargeVector_equal M]

/-- Equality of the ORIGINAL source topological closures of these two joint
charge graphs. This does not assert a Hamiltonian/operator self-adjointness
theorem or identify any separate physically selected spectral domain. -/
theorem sourceClosedJointChargeGraph_equal
    {N : ℕ} (M : AlgebraData N) :
    M.deformedClosedGraph 1 0 = M.fullClosedGraph := by
  change (M.deformedCoreGraph 1 0).topologicalClosure =
    M.fullCoreGraph.topologicalClosure
  rw [sourceCoreGraph_equal M]

/-- Exact source joint closed-charge domain agreement: for every L2 input,
membership in the domain of the genuine deformed closed graph iff membership
in the original full closed joint-charge graph. -/
theorem sourceClosedJointChargeDomain_iff
    {N : ℕ} (M : AlgebraData N) (ψ : FullL2 N) :
    (∃ y : SpinIndex → FullL2 N,
      (ψ,y) ∈ M.deformedClosedGraph 1 0) ↔
    (∃ y : SpinIndex → FullL2 N,
      (ψ,y) ∈ M.fullClosedGraph) := by
  rw [sourceClosedJointChargeGraph_equal M]

#print axioms sourceChargeMap_equal
#print axioms sourceChargeVector_equal
#print axioms sourceCoreGraph_equal
#print axioms sourceClosedJointChargeGraph_equal
#print axioms sourceClosedJointChargeDomain_iff

end
end FCP.BFSSSU2GaugeG4K10A
