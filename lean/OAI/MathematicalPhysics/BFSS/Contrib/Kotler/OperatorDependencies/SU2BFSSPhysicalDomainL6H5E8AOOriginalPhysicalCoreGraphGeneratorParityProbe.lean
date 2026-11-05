import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8ALOriginalFullL2PhysicalParityProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AMOriginalSourceChargeVectorParityProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8ANOriginalOppositeGammaGaugeDataProbe

/-!
# H5E8AO — exact original physical sixteen-charge CORE GRAPH generator parity

Previously accepted:
  AL: real original source parity maps the *gauge-invariant* SmoothCore.
  AM: the whole original sixteen-charge column is covariant under P₂.
  AN: real SU2 dependent GaugeData of the opposite gamma model has
      exactly the same physicalSpace and invariantCore.

This probe proves a genuine two-way correspondence between the
*actual original source gauge-restricted sixteen-charge core graph
GENERATORS* and the analogous opposite-gamma model generators.
It does not repackage a new BFSS operator or assume a closed-graph
equivalence. Closure, graph-domain and Hamiltonian operator-domain
theorems are separate and remain open until qualified.

Exact source original and Mathlib/Lean provenance required.
-/

set_option autoImplicit false
set_option maxHeartbeats 220000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AO
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AD
open FCP.BFSSSU2PhysicalDomainL6H5E8AF
open FCP.BFSSSU2PhysicalDomainL6H5E8AI
open FCP.BFSSSU2PhysicalDomainL6H5E8AL
open FCP.BFSSSU2PhysicalDomainL6H5E8AM
open FCP.BFSSSU2PhysicalDomainL6H5E8AN

/-- Spatial parity simultaneously transports source FullL2 input and
each literal spin-indexed FullL2 output. A *function* on graph pairs,
not (yet) a Hilbert product unitary. -/
noncomputable def originalPhysicalGraphPairParity {N : ℕ} :
    (FullL2 N × (SpinIndex → FullL2 N)) →
      FullL2 N × (SpinIndex → FullL2 N) :=
  fun p => (originalFullL2Parity p.1,
    fun α => originalFullL2Parity (p.2 α))

/-- Exact source G.invariantCore generator to the opposite-gamma
source gauge-invariant core generator, for all sixteen charge outputs. -/
theorem originalPhysicalCorePair_to_opposite {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) (f : G.invariantCore) :
    ∃ f' : (originalOppositeGammaGaugeData M G).invariantCore,
      (coreToL2 f'.val, (oppositeGamma M).chargeVector f'.val) =
        originalPhysicalGraphPairParity
          (coreToL2 f.val, M.chargeVector f.val) := by
  have hf : originalSmoothParity f.val ∈
      (originalOppositeGammaGaugeData M G).invariantCore := by
    rw [originalOppositeGammaGaugeData_invariantCore M G]
    exact originalSmoothParity_mem_invariantCore M G f
  refine ⟨⟨originalSmoothParity f.val, hf⟩, ?_⟩
  change
    (coreToL2 (originalSmoothParity f.val),
      (oppositeGamma M).chargeVector (originalSmoothParity f.val)) =
    (originalFullL2Parity (coreToL2 f.val),
      fun α => originalFullL2Parity ((M.chargeVector f.val) α))
  apply Prod.ext
  · exact (originalFullL2Parity_coreToL2 f.val).symm
  · exact originalChargeVector_parity M f.val

/-- Conversely every opposite-gamma physical source core generator
is the image of a genuine original source gauge-core generator.
The inverse uses the *accepted* involutive P on SmoothCore,
not a guessed gauge-space inverse. -/
theorem originalPhysicalCorePair_from_opposite {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (f' : (originalOppositeGammaGaugeData M G).invariantCore) :
    ∃ f : G.invariantCore,
      originalPhysicalGraphPairParity
        (coreToL2 f.val, M.chargeVector f.val) =
      (coreToL2 f'.val, (oppositeGamma M).chargeVector f'.val) := by
  have hcore : f'.val ∈ G.invariantCore := by
    rw [← originalOppositeGammaGaugeData_invariantCore M G]
    exact f'.property
  let f : G.invariantCore :=
    ⟨originalSmoothParity f'.val,
      originalSmoothParity_mem_invariantCore M G ⟨f'.val, hcore⟩⟩
  refine ⟨f, ?_⟩
  change
    (originalFullL2Parity (coreToL2 (originalSmoothParity f'.val)),
      fun α => originalFullL2Parity
        ((M.chargeVector (originalSmoothParity f'.val)) α)) =
    (coreToL2 f'.val, (oppositeGamma M).chargeVector f'.val)
  apply Prod.ext
  · calc
      originalFullL2Parity (coreToL2 (originalSmoothParity f'.val)) =
          coreToL2 (originalSmoothParity (originalSmoothParity f'.val)) :=
        originalFullL2Parity_coreToL2 _
      _ = coreToL2 f'.val := by
        rw [originalSmoothParity_twice]
  · have h := originalChargeVector_parity M (originalSmoothParity f'.val)
    rw [originalSmoothParity_twice] at h
    exact h.symm

#print axioms originalPhysicalGraphPairParity
#print axioms originalPhysicalCorePair_to_opposite
#print axioms originalPhysicalCorePair_from_opposite

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AO
