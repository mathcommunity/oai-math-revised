import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V30Real48CliffordGeneratorInjectiveViaExteriorProbe

/-! Owner import from FCP cc608e2282e1b32bb11bbb64424e4775b28138e2,
original source blob d6e025372d9f3a393dbb21ba7700c0bc95fd40f2.
Only imports and this provenance comment are adapted. Definitions, theorem
statements and proof bodies below are source-exact. Local candidate only
until an independent owner strict gate passes. -/

/-!
S1V31 — canonical actual source-sized real-vector action induced by
EVERY element of the genuine Clifford-algebra Spin(48) group.

S1V29 proves that arbitrary Spin conjugation preserves the image of
the ORIGINAL source48 real Clifford generator; S1V30 proves that same
generator is injective. Thus every conjugated generator has exactly
one underlying REAL source48 vector. The action is defined by this
unique existence, not by a postulated independent SO48 map.

This NEW source is UNCOMPILED until its strict three-root Gate #1.
No additional Clifford faithfulness or Hilbert assumptions. Its
claims do NOT yet prove the action's group law, quadratic isometry,
determinant +1, continuity, double covering, global SU2 lift or
BFSS mass gap.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000

namespace FCP.BFSSS1V31
noncomputable section

open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- For ALL genuine source Spin48 elements and ALL source real 48-vectors,
there is exactly one source vector representing its Clifford-conjugated
degree-one generator, without an assumed target SO48 action. -/
theorem every_sourceSpin48_conjugated_generator_unique
    (s : spinGroup Q) (v : Source48Vector) :
    ∃! w : Source48Vector,
      CliffordAlgebra.ι Q w =
        ConjAct.toConjAct (spinGroup.toUnits s) •
          (CliffordAlgebra.ι Q v) := by
  obtain ⟨w, hw⟩ :=
    FCP.BFSSS1V29.all_sourceSpin48_generators_stay_real s v
  refine ⟨w, hw, ?_⟩
  intro y hy
  exact FCP.BFSSS1V30.source48_cliffordGenerator_injective
    (hy.trans hw.symm)

/-- The unique real 48-vector represented by the conjugated Clifford
generator. Defined from the proven existence/uniqueness, not a choice
of group lift or a source-matrix replacement. -/
noncomputable def sourceSpin48VectorAction
    (s : spinGroup Q) (v : Source48Vector) : Source48Vector :=
  Classical.choose (every_sourceSpin48_conjugated_generator_unique s v).exists

theorem sourceSpin48VectorAction_clifford_generator
    (s : spinGroup Q) (v : Source48Vector) :
    CliffordAlgebra.ι Q (sourceSpin48VectorAction s v) =
      ConjAct.toConjAct (spinGroup.toUnits s) •
        (CliffordAlgebra.ι Q v) := by
  exact Classical.choose_spec
    (every_sourceSpin48_conjugated_generator_unique s v).exists

/-- The actual source real-vector action is additive for every Spin48
element, transported through the injective source Clifford generator
and the additive conjugation action of Clifford units. -/
theorem sourceSpin48VectorAction_add
    (s : spinGroup Q) (v w : Source48Vector) :
    sourceSpin48VectorAction s (v + w) =
      sourceSpin48VectorAction s v + sourceSpin48VectorAction s w := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q (sourceSpin48VectorAction s (v + w)) =
        ConjAct.toConjAct (spinGroup.toUnits s) •
          (CliffordAlgebra.ι Q (v + w)) :=
      sourceSpin48VectorAction_clifford_generator s (v + w)
    _ =
        (ConjAct.toConjAct (spinGroup.toUnits s) • (CliffordAlgebra.ι Q v)) +
        (ConjAct.toConjAct (spinGroup.toUnits s) • (CliffordAlgebra.ι Q w)) := by
      rw [map_add, smul_add]
    _ =
        CliffordAlgebra.ι Q
          (sourceSpin48VectorAction s v + sourceSpin48VectorAction s w) := by
      rw [map_add, sourceSpin48VectorAction_clifford_generator,
        sourceSpin48VectorAction_clifford_generator]

#print axioms every_sourceSpin48_conjugated_generator_unique
#print axioms sourceSpin48VectorAction_clifford_generator
#print axioms sourceSpin48VectorAction_add

end
end FCP.BFSSS1V31
