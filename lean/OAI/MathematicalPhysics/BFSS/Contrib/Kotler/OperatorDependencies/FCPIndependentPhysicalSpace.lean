import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentFullL2Unitary

/-!
M4C3 — independent physical gauge-constraint space versus the literal
original BFSS GaugeData.physicalSpace.

The independent fermionic representation is constructed without choosing J.
The bosonic pullback is the literal source pullback for the common R^27
configuration space. This gate uses both separate M4C1 intertwining lemmas
and the M4C2 full-L2 unitary. No composite group-action convention, smooth
core, unbounded-operator, Hamiltonian, Spin9, or spectrum assertion is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.IndependentPhysicalSpace
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentOriginalGaugeBridge
open FCP.IndependentFullL2GaugeTransport
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private abbrev μ := (volume : Measure (Boson 2))

/-- Source bosonic pullback on the independent finite-fiber L2 space.
This is specified before any choice of generator-preserving unitary J. -/
def independentBosonPullback (g : GaugeGroup 2) : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (pairedGaugeData.boson g)
    (pairedGaugeData.boson g).measurePreserving).toContinuousLinearMap

/-- Expand the actual source kernel intersection, rather than replacing it
with a transported definition or an assumed combined-action fixed space. -/
theorem originalPhysicalSpace_mem_iff (v : FullL2 2) :
    v ∈ pairedGaugeData.physicalSpace ↔
      ∀ g : GaugeGroup 2,
        pairedGaugeData.bosonPullback g v = pairedGaugeData.fiberAction g v := by
  simp only [AlgebraData.GaugeData.physicalSpace, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]

variable [FiniteDimensional ℂ E]

variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
  theta α A * theta β B + theta β B * theta α A =
    (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
variable (hHermitian : ∀ α A, (theta α A).IsSymmetric)

/-- The genuinely independent M4B native-Spin fermion representation,
acting pointwise on E-valued L2 equivalence classes. -/
def independentFermionAction (g : GaugeGroup 2) : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  (independentOriginalGaugeHom theta hCAR hHermitian g).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    2 μ

/-- Independent gauge constraints, defined without a chosen J or reference
to the original source physicalSpace. -/
def independentPhysicalSpace : Submodule ℂ (Lp E 2 μ) :=
  ⨅ g : GaugeGroup 2,
    LinearMap.ker
      ((independentBosonPullback (E := E) g).toLinearMap -
        (independentFermionAction theta hCAR hHermitian g).toLinearMap)

/-- Expand the independently specified kernel intersection. -/
theorem independentPhysicalSpace_mem_iff (v : Lp E 2 μ) :
    v ∈ independentPhysicalSpace theta hCAR hHermitian ↔
      ∀ g : GaugeGroup 2,
        independentBosonPullback (E := E) g v =
          independentFermionAction theta hCAR hHermitian g v := by
  simp only [independentPhysicalSpace, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

/-- Exact two-way identification of independently defined physical gauge
constraints with the ORIGINAL source GaugeData.physicalSpace. The unitary J
must preserve all 48 source Majorana labels. Neither gauge action is defined
by transporting the other's physicalSpace. -/
theorem independentPhysicalSpace_iff_source
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (v : Lp E 2 μ) :
    v ∈ independentPhysicalSpace theta hCAR hHermitian ↔
      fiberTransport J v ∈ pairedGaugeData.physicalSpace := by
  constructor
  · intro hv
    apply (originalPhysicalSpace_mem_iff (fiberTransport J v)).2
    intro g
    have hp := (independentPhysicalSpace_mem_iff theta hCAR hHermitian v).1 hv g
    calc
      pairedGaugeData.bosonPullback g (fiberTransport J v) =
          fiberTransport J (independentBosonPullback (E := E) g v) := by
            exact (fiberTransport_bosonPullback J g v).symm
      _ = fiberTransport J (independentFermionAction theta hCAR hHermitian g v) :=
        congrArg (fiberTransport J) hp
      _ = pairedGaugeData.fiberAction g (fiberTransport J v) :=
        fiberTransport_fermionGauge theta hCAR hHermitian J hJ g v
  · intro hv
    apply (independentPhysicalSpace_mem_iff theta hCAR hHermitian v).2
    intro g
    apply (fiberTransportUnitary J).injective
    change fiberTransport J (independentBosonPullback (E := E) g v) =
      fiberTransport J (independentFermionAction theta hCAR hHermitian g v)
    calc
      fiberTransport J (independentBosonPullback (E := E) g v) =
          pairedGaugeData.bosonPullback g (fiberTransport J v) :=
            fiberTransport_bosonPullback J g v
      _ = pairedGaugeData.fiberAction g (fiberTransport J v) :=
        (originalPhysicalSpace_mem_iff (fiberTransport J v)).1 hv g
      _ = fiberTransport J (independentFermionAction theta hCAR hHermitian g v) :=
        (fiberTransport_fermionGauge theta hCAR hHermitian J hJ g v).symm

#print axioms independentBosonPullback
#print axioms originalPhysicalSpace_mem_iff
#print axioms independentFermionAction
#print axioms independentPhysicalSpace
#print axioms independentPhysicalSpace_mem_iff
#print axioms independentPhysicalSpace_iff_source

end
end FCP.IndependentPhysicalSpace
