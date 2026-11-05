import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4JExactGaugeDataAssemblyProbe

/-!
# BFSS SU(2) G4-K1 — physical Gauss subspace and invariant smooth core

From the exact six-field pairedGaugeData (accepted Gate #127),
instantiate the PINNED upstream BFSS GaugeData.physicalSpace
and its already proved generic source properties on the actual
BFSS N=2 full L² Hilbert type.

This proof checks closedness, and literal pointwise equivariance and
norm invariance of smooth sections already belonging to the invariant
core. It does NOT assert the physical space or core is nonzero, dense,
has an eigenstate, or supports a new Hamiltonian spectral theorem.

No auxiliary gauge action or new algebra witness is introduced.
-/

namespace FCP.BFSSSU2GaugeG4K1
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG2A
open FCP.BFSSSU2GaugeG4E FCP.BFSSSU2GaugeG4J

/-- Literal pinned Gauss-invariant physical Hilbert submodule
associated with the newly constructed *concrete* SU(2) GaugeData. -/
noncomputable def pairedPhysicalSpace : Submodule ℂ (FullL2 2) :=
  pairedGaugeData.physicalSpace

/-- The physical Hilbert subspace for the actual source-bound
SU(2) paired gauge action is topologically closed. This is a
specialization of the existing upstream GaugeCore theorem. -/
theorem pairedPhysicalSpace_closed :
    IsClosed (pairedPhysicalSpace : Set (FullL2 2)) := by
  exact pairedGaugeData.physicalSpace_closed

/-- Every smooth section in this literal Gauss-invariant core is
pointwise equivariant under the previously certified actions. -/
theorem pairedInvariantCore_equivariant
    (f : pairedGaugeData.invariantCore)
    (g : GaugeGroup 2) (x : Boson 2) :
    f.val (bosonGauge g x) =
      fermionGaugeUnitaryHom g (f.val x) := by
  change f.val (pairedGaugeData.boson g x) =
    pairedGaugeData.fermion g (f.val x)
  exact pairedGaugeData.invariantCore_equivariant f g x

/-- The exact fermion state norm along a physical-core section is
constant along the genuine SU(2) bosonic gauge orbit. -/
theorem pairedInvariantCore_norm_gauge
    (f : pairedGaugeData.invariantCore)
    (g : GaugeGroup 2) (x : Boson 2) :
    ‖f.val (bosonGauge g x)‖ = ‖f.val x‖ := by
  change ‖f.val (pairedGaugeData.boson g x)‖ = ‖f.val x‖
  exact pairedGaugeData.invariantCore_norm_gauge f g x

#print axioms pairedPhysicalSpace
#print axioms pairedPhysicalSpace_closed
#print axioms pairedInvariantCore_equivariant
#print axioms pairedInvariantCore_norm_gauge

end
end FCP.BFSSSU2GaugeG4K1
