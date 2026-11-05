import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V39Original48CliffordGeneratorMatrixActionProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V30Real48CliffordGeneratorInjectiveViaExteriorProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

/-!
S1V40 — original source-sized REAL vector action of the genuinely defined
lipschitzGroup source48Quadratic (subgroup of actual Clifford units).

Uses pinned Mathlib conjugation-range theorem, the previously accepted
source48 Clifford-generator injectivity, and direct real scalar linearity.
This is NOT a surrogate vector representation. No group homomorphism,
determinant parity, SO48 projection, covering, global SU2 lift,
manuscript correspondence or spectral claim is asserted.

The four theorem roots remain UNQUALIFIED until strict CI passes.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000

namespace FCP.BFSSS1V40
noncomputable section

open FCP.BFSSS1V0
open scoped Pointwise

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Each genuine Lipschitz unit conjugates every ORIGINAL Clifford source
generator into EXACTLY ONE original real 48-vector. -/
theorem sourceLipschitz48_conjugated_generator_unique
    (x : lipschitzGroup Q) (v : Source48Vector) :
    ∃! w : Source48Vector,
      CliffordAlgebra.ι Q w =
        ConjAct.toConjAct (x : (CliffordAlgebra Q)ˣ) •
          (CliffordAlgebra.ι Q v) := by
  obtain ⟨w, hw⟩ :=
    lipschitzGroup.conjAct_smul_ι_mem_range_ι x.property v
  refine ⟨w, hw, ?_⟩
  intro y hy
  exact FCP.BFSSS1V30.source48_cliffordGenerator_injective
    (hy.trans hw.symm)

/-- The true original source 48-real action of a genuine Lipschitz unit,
selected only from proven existence and Clifford-injectivity. -/
noncomputable def sourceLipschitz48VectorAction
    (x : lipschitzGroup Q) (v : Source48Vector) : Source48Vector :=
  Classical.choose (sourceLipschitz48_conjugated_generator_unique x v).exists

/-- Definition exactly agrees with the actual Clifford conjugation of
source degree-one generators, for every true Lipschitz unit and vector. -/
theorem sourceLipschitz48VectorAction_clifford
    (x : lipschitzGroup Q) (v : Source48Vector) :
    CliffordAlgebra.ι Q (sourceLipschitz48VectorAction x v) =
      ConjAct.toConjAct (x : (CliffordAlgebra Q)ˣ) •
        (CliffordAlgebra.ι Q v) := by
  exact Classical.choose_spec
    (sourceLipschitz48_conjugated_generator_unique x v).exists

/-- Actual Clifford-defined source Lipschitz vector action preserves
addition; this is NOT a separately assumed GL representation. -/
theorem sourceLipschitz48VectorAction_add
    (x : lipschitzGroup Q) (v w : Source48Vector) :
    sourceLipschitz48VectorAction x (v + w) =
      sourceLipschitz48VectorAction x v +
        sourceLipschitz48VectorAction x w := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q (sourceLipschitz48VectorAction x (v + w)) =
        ConjAct.toConjAct (x : (CliffordAlgebra Q)ˣ) •
          (CliffordAlgebra.ι Q (v + w)) :=
      sourceLipschitz48VectorAction_clifford x (v + w)
    _ =
        (ConjAct.toConjAct (x : (CliffordAlgebra Q)ˣ) •
          (CliffordAlgebra.ι Q v)) +
        (ConjAct.toConjAct (x : (CliffordAlgebra Q)ˣ) •
          (CliffordAlgebra.ι Q w)) := by
      rw [map_add, smul_add]
    _ =
        CliffordAlgebra.ι Q
          (sourceLipschitz48VectorAction x v +
            sourceLipschitz48VectorAction x w) := by
      rw [map_add, sourceLipschitz48VectorAction_clifford,
        sourceLipschitz48VectorAction_clifford]

/-- Real scalar linearity for the original source Lipschitz action,
without projecting to a guessed orthogonal representation. -/
theorem sourceLipschitz48VectorAction_smul
    (x : lipschitzGroup Q) (a : ℝ) (v : Source48Vector) :
    sourceLipschitz48VectorAction x (a • v) =
      a • sourceLipschitz48VectorAction x v := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q (sourceLipschitz48VectorAction x (a • v)) =
        ConjAct.toConjAct (x : (CliffordAlgebra Q)ˣ) •
          (CliffordAlgebra.ι Q (a • v)) :=
      sourceLipschitz48VectorAction_clifford x (a • v)
    _ = a • (ConjAct.toConjAct (x : (CliffordAlgebra Q)ˣ) •
        (CliffordAlgebra.ι Q v)) := by
      rw [map_smul, smul_comm]
    _ = CliffordAlgebra.ι Q (a • sourceLipschitz48VectorAction x v) := by
      rw [map_smul, sourceLipschitz48VectorAction_clifford]

#print axioms sourceLipschitz48_conjugated_generator_unique
#print axioms sourceLipschitz48VectorAction_clifford
#print axioms sourceLipschitz48VectorAction_add
#print axioms sourceLipschitz48VectorAction_smul

end
end FCP.BFSSS1V40
