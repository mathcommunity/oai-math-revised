import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D11OriginalSpin48ExactTwoSignKernel

/-!
K1D12 — original source Spin48 action laws, with NO replacement action.

The original S1V31 source action comes from the unique source real
vector corresponding to conjugation of each source Clifford generator.
S1V31 already proves additivity; K1D11 proves the exact two-sign
pointwise fixer set and identity action.

New obligations: scalar linearity on real source48 vectors and
multiplicativity in the ACTUAL source Spin48 group. Transport through
the same source-defined injective Clifford generator, using pinned
Mathlib ConjAct units action and spinGroup.toUnits homomorphism.

These facts do not construct an SO48 target, assert determinant +1,
prove image surjectivity, a topological covering, a Spin9 global lift,
or BFSS spectra. CANDIDATE pending independent strict source CI.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace FCP.BFSSS1V52K1D12
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- The original source Spin48 vector action commutes with real scalar
multiplication. The only action used is sourceSpin48VectorAction. -/
theorem originalSourceSpin48VectorAction_smul
    (s : spinGroup Q) (r : ℝ) (v : Source48Vector) :
    FCP.BFSSS1V31.sourceSpin48VectorAction s (r • v) =
      r • FCP.BFSSS1V31.sourceSpin48VectorAction s v := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q
        (FCP.BFSSS1V31.sourceSpin48VectorAction s (r • v)) =
        ConjAct.toConjAct (spinGroup.toUnits s) •
          (CliffordAlgebra.ι Q (r • v)) :=
      FCP.BFSSS1V31.sourceSpin48VectorAction_clifford_generator s (r • v)
    _ = r • (ConjAct.toConjAct (spinGroup.toUnits s) •
          (CliffordAlgebra.ι Q v)) := by
      rw [map_smul]
      exact (smul_comm r (ConjAct.toConjAct (spinGroup.toUnits s))
        (CliffordAlgebra.ι Q v)).symm
    _ = CliffordAlgebra.ι Q
          (r • FCP.BFSSS1V31.sourceSpin48VectorAction s v) := by
      rw [map_smul, FCP.BFSSS1V31.sourceSpin48VectorAction_clifford_generator]

/-- The exact S1V31 source vector action respects multiplication of
actual elements of Mathlib's source Spin48 subtype. -/
theorem originalSourceSpin48VectorAction_mul
    (s t : spinGroup Q) (v : Source48Vector) :
    FCP.BFSSS1V31.sourceSpin48VectorAction (s * t) v =
      FCP.BFSSS1V31.sourceSpin48VectorAction s
        (FCP.BFSSS1V31.sourceSpin48VectorAction t v) := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q
        (FCP.BFSSS1V31.sourceSpin48VectorAction (s * t) v) =
        ConjAct.toConjAct (spinGroup.toUnits (s * t)) •
          (CliffordAlgebra.ι Q v) :=
      FCP.BFSSS1V31.sourceSpin48VectorAction_clifford_generator (s * t) v
    _ = ConjAct.toConjAct (spinGroup.toUnits s) •
          (ConjAct.toConjAct (spinGroup.toUnits t) •
            (CliffordAlgebra.ι Q v)) := by
      rw [map_mul, map_mul, mul_smul]
    _ = CliffordAlgebra.ι Q
          (FCP.BFSSS1V31.sourceSpin48VectorAction s
            (FCP.BFSSS1V31.sourceSpin48VectorAction t v)) := by
      rw [FCP.BFSSS1V31.sourceSpin48VectorAction_clifford_generator,
        FCP.BFSSS1V31.sourceSpin48VectorAction_clifford_generator]

#print axioms originalSourceSpin48VectorAction_smul
#print axioms originalSourceSpin48VectorAction_mul

end
end FCP.BFSSS1V52K1D12
