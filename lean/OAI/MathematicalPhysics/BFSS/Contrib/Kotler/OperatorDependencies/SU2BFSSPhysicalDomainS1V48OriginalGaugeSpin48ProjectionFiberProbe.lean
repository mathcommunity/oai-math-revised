import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V47ActualSpin48RealDetOrientationProbe

/-!
S1V48: exact source SU(2)-to-Spin(48) lift compatibility predicate.

S1J's ORIGINAL +i SU2 source 48-real paired-Majorana matrix and
S1V31's genuine Spin48 Clifford-conjugation vector action share
the LITERAL Fin 24 × Fin 2 real label type. Prove the identity,
multiplication and inverse compatibility of this SAME-source
predicate, without inventing a continuous lift or covering map.

No pointwise quarter-turn witness, covering-space topology, kernel
identification, manuscript Hilbert intertwiner, or spectral result
is asserted by these declarations.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V48
noncomputable section

open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Exact SO-matrix compatibility criterion for a FUTURE Spin lift,
referencing original source SU2 color/Fock-Majorana labels and the
genuine original Spin48 Clifford action. No existence assertion. -/
def sourceSpin48CoversActualGauge
    (g : GaugeGroup 2) (s : spinGroup Q) : Prop :=
  ∀ v : Source48Vector,
    FCP.BFSSS1V31.sourceSpin48VectorAction s v =
      (FCP.BFSSSU2PhysicalDomainS1J.sourceRealMajoranaMatrix g).mulVec v

/-- The actual identity gauge matrix is covered by actual Spin identity. -/
theorem sourceSpin48CoversActualGauge_one :
    sourceSpin48CoversActualGauge (1 : GaugeGroup 2)
      (1 : spinGroup Q) := by
  intro v
  change FCP.BFSSS1V31.sourceSpin48VectorAction (1 : spinGroup Q) v =
    (FCP.BFSSSU2PhysicalDomainS1J.sourceRealMajoranaMatrix
      (1 : GaugeGroup 2)).mulVec v
  rw [FCP.BFSSS1V32.sourceSpin48VectorAction_one,
    FCP.BFSSSU2PhysicalDomainS1J.sourceRealMajoranaMatrix_one,
    Matrix.one_mulVec]

/-- If actual Spin s covers the actual SU2 gauge matrix g and t covers h,
their group products retain the EXACT original 48-real projection relation. -/
theorem sourceSpin48CoversActualGauge_mul
    {g h : GaugeGroup 2} {s t : spinGroup Q}
    (hs : sourceSpin48CoversActualGauge g s)
    (ht : sourceSpin48CoversActualGauge h t) :
    sourceSpin48CoversActualGauge (g * h) (s * t) := by
  intro v
  calc
    FCP.BFSSS1V31.sourceSpin48VectorAction (s * t) v =
        FCP.BFSSS1V31.sourceSpin48VectorAction s
          (FCP.BFSSS1V31.sourceSpin48VectorAction t v) :=
      FCP.BFSSS1V32.sourceSpin48VectorAction_mul s t v
    _ = FCP.BFSSS1V31.sourceSpin48VectorAction s
          ((FCP.BFSSSU2PhysicalDomainS1J.sourceRealMajoranaMatrix h).mulVec v) := by
      rw [ht v]
    _ = (FCP.BFSSSU2PhysicalDomainS1J.sourceRealMajoranaMatrix g).mulVec
          ((FCP.BFSSSU2PhysicalDomainS1J.sourceRealMajoranaMatrix h).mulVec v) :=
      hs _
    _ = (FCP.BFSSSU2PhysicalDomainS1J.sourceRealMajoranaMatrix (g * h)).mulVec v := by
      rw [FCP.BFSSSU2PhysicalDomainS1J.sourceRealMajoranaMatrix_mul,
        Matrix.mulVec_mulVec]

/-- Inversion stability for the exact same-source lift fiber.
This follows from the two genuine group actions, not a choice of
Spin lift or topological surjectivity. -/
theorem sourceSpin48CoversActualGauge_inv
    {g : GaugeGroup 2} {s : spinGroup Q}
    (hs : sourceSpin48CoversActualGauge g s) :
    sourceSpin48CoversActualGauge g⁻¹ s⁻¹ := by
  intro v
  have hpre :
      FCP.BFSSS1V31.sourceSpin48VectorAction s
        ((FCP.BFSSSU2PhysicalDomainS1J.sourceRealMajoranaMatrix g⁻¹).mulVec v) = v := by
    calc
      FCP.BFSSS1V31.sourceSpin48VectorAction s
          ((FCP.BFSSSU2PhysicalDomainS1J.sourceRealMajoranaMatrix g⁻¹).mulVec v) =
        (FCP.BFSSSU2PhysicalDomainS1J.sourceRealMajoranaMatrix g).mulVec
          ((FCP.BFSSSU2PhysicalDomainS1J.sourceRealMajoranaMatrix g⁻¹).mulVec v) :=
        hs _
      _ = v := by
        rw [Matrix.mulVec_mulVec,
          ← FCP.BFSSSU2PhysicalDomainS1J.sourceRealMajoranaMatrix_mul,
          mul_inv_cancel,
          FCP.BFSSSU2PhysicalDomainS1J.sourceRealMajoranaMatrix_one,
          Matrix.one_mulVec]
  calc
    FCP.BFSSS1V31.sourceSpin48VectorAction s⁻¹ v =
        FCP.BFSSS1V31.sourceSpin48VectorAction s⁻¹
          (FCP.BFSSS1V31.sourceSpin48VectorAction s
            ((FCP.BFSSSU2PhysicalDomainS1J.sourceRealMajoranaMatrix g⁻¹).mulVec v)) := by
      rw [hpre]
    _ = (FCP.BFSSSU2PhysicalDomainS1J.sourceRealMajoranaMatrix g⁻¹).mulVec v := by
      rw [← FCP.BFSSS1V32.sourceSpin48VectorAction_mul,
        inv_mul_cancel, FCP.BFSSS1V32.sourceSpin48VectorAction_one]

#print axioms sourceSpin48CoversActualGauge
#print axioms sourceSpin48CoversActualGauge_one
#print axioms sourceSpin48CoversActualGauge_mul
#print axioms sourceSpin48CoversActualGauge_inv

end
end FCP.BFSSS1V48
