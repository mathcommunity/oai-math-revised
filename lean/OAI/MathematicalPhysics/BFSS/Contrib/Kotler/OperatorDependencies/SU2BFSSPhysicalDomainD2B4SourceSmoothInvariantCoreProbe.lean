import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B3JJointOperatorSmoothHaarProbe

/-!
# BFSS SU2 D2B4: exact-source Haar projection into the physical smooth core

PROSPECTIVE / UNCOMPILED until the pinned GitHub Actions gate passes.
Use only the original BFSS SmoothCore = TestFunction ⊤ (Fermion 2) ⊤,
the original GaugeData.bosonPullback/fiberAction maps, and the
ACTUAL true SU2 Haar average from the accepted D2B1–D2B3J proofs.

No invented projection or finite-dimensional gauge replacement.
L² contractivity and density are NOT proved in this file.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B4
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open OAI.Laughlin.Rotation
open FCP.BFSSSU2PhysicalDomainD2B1
open FCP.BFSSSU2PhysicalDomainD2B2
open FCP.BFSSSU2PhysicalDomainD2B3J
open MeasureTheory
open scoped Topology ContDiff

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- Bundle the EXACT source Haar integral in the ORIGINAL
BFSS SmoothCore/TestFunction object. Smoothness is the
unconditional accepted D2B3J theorem; compact support is
the independent accepted D2B2 theorem. -/
noncomputable def sourceHaarAverageCore (f : SmoothCore 2) : SmoothCore 2 :=
  ⟨sourceHaarAverageRaw M G f,
    sourceHaarAverageRaw_contDiff M G f,
    sourceHaarAverageRaw_hasCompactSupport M G f,
    by intro x hx; trivial⟩

theorem sourceHaarAverageCore_apply (f : SmoothCore 2) (x : Boson 2) :
    sourceHaarAverageCore M G f x = sourceHaarAverageRaw M G f x := rfl

/-- This is the actual BFSS boson/fermion representation
pointwise equivariance of the newly BUNDLED source function. -/
theorem sourceHaarAverageCore_equivariant
    (f : SmoothCore 2) (g : GaugeGroup 2) (x : Boson 2) :
    sourceHaarAverageCore M G f (G.boson g x) =
      G.fermion g (sourceHaarAverageCore M G f x) := by
  change sourceHaarAverageRaw M G f (G.boson g x) =
    G.fermion g (sourceHaarAverageRaw M G f x)
  exact sourceHaarAverageRaw_equivariant M G f g x

/-- The source bundled average lies in the EXACT source physical
submodule, not just the space of pointwise invariant functions.
The proof passes through the source coreToL2 map and proves equality
of its real source boson pullback and fermion Lp action. -/
theorem sourceHaarAverageCore_mem_physicalSpace
    (f : SmoothCore 2) :
    coreToL2 (sourceHaarAverageCore M G f) ∈ G.physicalSpace := by
  let a : SmoothCore 2 := sourceHaarAverageCore M G f
  change coreToL2 a ∈
    (⨅ g : GaugeGroup 2,
      LinearMap.ker (G.bosonPullback g - G.fiberAction g))
  apply (Submodule.mem_iInf _).mpr
  intro g
  change G.bosonPullback g (coreToL2 a) -
    G.fiberAction g (coreToL2 a) = 0
  apply sub_eq_zero.mpr
  apply Lp.ext
  have hb := Lp.coeFn_compMeasurePreserving (coreToL2 a)
    (G.boson g).measurePreserving
  have hf := ContinuousLinearMap.coeFn_compLp
    (G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap (coreToL2 a)
  have ha := coreToL2_ae a
  have hac := ha.comp_tendsto
    (G.boson g).measurePreserving.quasiMeasurePreserving.tendsto_ae
  filter_upwards [hb, hf, ha, hac] with x hbx hfx hax hacx
  calc
    (G.bosonPullback g (coreToL2 a)) x =
        (coreToL2 a) (G.boson g x) := hbx
    _ = a (G.boson g x) := hacx
    _ = G.fermion g (a x) :=
      sourceHaarAverageCore_equivariant M G f g x
    _ = G.fermion g ((coreToL2 a) x) := congrArg (G.fermion g) hax.symm
    _ = (G.fiberAction g (coreToL2 a)) x := hfx.symm

/-- Membership in the original source invariantCore is DEFINED by
its physicalSpace-comap under coreToL2. -/
theorem sourceHaarAverageCore_mem_invariantCore
    (f : SmoothCore 2) :
    sourceHaarAverageCore M G f ∈ G.invariantCore := by
  change coreToL2 (sourceHaarAverageCore M G f) ∈ G.physicalSpace
  exact sourceHaarAverageCore_mem_physicalSpace M G f

/-- Genuine Haar averaging fixes any ALREADY source-defined
invariant smooth-core section; derived from accepted D2B1,
not an assumed projection law. -/
theorem sourceHaarAverageCore_fixed
    (f : G.invariantCore) :
    sourceHaarAverageCore M G f.val = f.val := by
  -- TestFunction.ext asks for whole Fermion-valued function equality.
  -- Generic `ext x` descended into PiLp coordinates in Gate #22.
  apply TestFunction.ext
  intro x
  change sourceHaarAverageRaw M G f.val x = f.val x
  exact sourceHaarAverageRaw_fixed M G f x

#print axioms sourceHaarAverageCore_apply
#print axioms sourceHaarAverageCore_equivariant
#print axioms sourceHaarAverageCore_mem_physicalSpace
#print axioms sourceHaarAverageCore_mem_invariantCore
#print axioms sourceHaarAverageCore_fixed

end
end FCP.BFSSSU2PhysicalDomainD2B4
