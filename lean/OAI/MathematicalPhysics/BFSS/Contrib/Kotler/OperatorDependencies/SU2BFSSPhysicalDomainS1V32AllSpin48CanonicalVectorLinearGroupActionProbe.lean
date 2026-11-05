import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V31CanonicalAllSpin48RealVectorActionProbe

/-!
S1V32 — first generic source-sized REAL linear and group-law interface
for EVERY genuine spinGroup source48Quadratic element.

Builds entirely upon the axiom-clean, accepted S1V31 canonical action,
defined through source Clifford ι and its S1V30 injectivity. Prove
real scalar linearity, identity and multiplication compatibility
without postulating an external Spin→SO map. Real source size and
all original index conventions are unchanged.

UNCOMPILED candidate: cannot assert these three roots until a strict
fresh Lean gate validates the original pins, their #print axioms and
cache-save. This is not yet quadratic preservation, det +1, an
orthogonal-group projection, covering, global Spin lift or BFSS gap.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000

namespace FCP.BFSSS1V32
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V31

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Every actual source Spin48 element acts REAL scalarly on the
original 48-vector, as proved through the ACTUAL Clifford generator. -/
theorem sourceSpin48VectorAction_smul
    (s : spinGroup Q) (a : ℝ) (v : Source48Vector) :
    sourceSpin48VectorAction s (a • v) =
      a • sourceSpin48VectorAction s v := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q (sourceSpin48VectorAction s (a • v)) =
        ConjAct.toConjAct (spinGroup.toUnits s) •
          (CliffordAlgebra.ι Q (a • v)) :=
      sourceSpin48VectorAction_clifford_generator s (a • v)
    _ = a • (ConjAct.toConjAct (spinGroup.toUnits s) •
          (CliffordAlgebra.ι Q v)) := by
      rw [map_smul, smul_comm]
    _ = CliffordAlgebra.ι Q (a • sourceSpin48VectorAction s v) := by
      rw [map_smul, sourceSpin48VectorAction_clifford_generator]

/-- The Clifford-defined canonical real-vector action of the genuine
source Spin48 identity is exactly the real-vector identity. -/
theorem sourceSpin48VectorAction_one (v : Source48Vector) :
    sourceSpin48VectorAction (1 : spinGroup Q) v = v := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q (sourceSpin48VectorAction (1 : spinGroup Q) v) =
        ConjAct.toConjAct (spinGroup.toUnits (1 : spinGroup Q)) •
          (CliffordAlgebra.ι Q v) :=
      sourceSpin48VectorAction_clifford_generator (1 : spinGroup Q) v
    _ = CliffordAlgebra.ι Q v := by simp

/-- True composition compatibility for arbitrary genuine Spin48
elements, transported through the injective original Clifford ι.
No new group-lift or independent SO matrix is assumed. -/
theorem sourceSpin48VectorAction_mul
    (s t : spinGroup Q) (v : Source48Vector) :
    sourceSpin48VectorAction (s * t) v =
      sourceSpin48VectorAction s (sourceSpin48VectorAction t v) := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q (sourceSpin48VectorAction (s * t) v) =
        ConjAct.toConjAct (spinGroup.toUnits (s * t)) •
          (CliffordAlgebra.ι Q v) :=
      sourceSpin48VectorAction_clifford_generator (s * t) v
    _ =
        ConjAct.toConjAct (spinGroup.toUnits s) •
          (ConjAct.toConjAct (spinGroup.toUnits t) •
            (CliffordAlgebra.ι Q v)) := by
      rw [map_mul, ConjAct.toConjAct_mul, mul_smul]
    _ =
        CliffordAlgebra.ι Q
          (sourceSpin48VectorAction s (sourceSpin48VectorAction t v)) := by
      rw [sourceSpin48VectorAction_clifford_generator,
        sourceSpin48VectorAction_clifford_generator]

#print axioms sourceSpin48VectorAction_smul
#print axioms sourceSpin48VectorAction_one
#print axioms sourceSpin48VectorAction_mul

end
end FCP.BFSSS1V32
