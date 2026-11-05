import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V31CanonicalAllSpin48RealVectorActionProbe

/-! Owner import from FCP cc608e2282e1b32bb11bbb64424e4775b28138e2,
original source blob 5d1117d1f469a3a76a78c3c4ae4b8896b18b1b7a.
Only imports and this provenance comment are adapted. Definitions, theorem
statements and proof bodies below are source-exact. Local candidate only
until an independent owner strict gate passes. -/

/-!
BFSS K1A — source-exact kernel commutation equivalence.

Reuses accepted original Clifford-generator injectivity, vector action,
and genuine source Spin48 group topology; proves equivalence of
trivial action and commutation with ALL actual original generators.
It does NOT establish that the commutant is scalar or classify the
kernel. The independent negative source Spin sign is staged as K1B.

STAGED until strict Lean 4.34.1 compilation and allowed-axiom gate.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000

namespace FCP.BFSSS1V52K1A
noncomputable section

open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Triviality of the ACTUAL original Clifford Spin48 vector action
is equivalent to commuting with EVERY true original source generator. -/
theorem originalSourceSpin48_trivialAction_iff_generator_commutes
    (s : spinGroup Q) :
    (∀ v : Source48Vector,
      FCP.BFSSS1V31.sourceSpin48VectorAction s v = v) ↔
    (∀ v : Source48Vector,
      (s : C) * CliffordAlgebra.ι Q v =
        CliffordAlgebra.ι Q v * (s : C)) := by
  have hstar : star (s : C) * (s : C) = 1 :=
    spinGroup.star_mul_self_of_mem s.property
  have hunit : (s : C) * star (s : C) = 1 :=
    spinGroup.mul_star_self_of_mem s.property
  have hsrc (v : Source48Vector) :
      CliffordAlgebra.ι Q
          (FCP.BFSSS1V31.sourceSpin48VectorAction s v) =
        (s : C) * CliffordAlgebra.ι Q v * star (s : C) := by
    have h := FCP.BFSSS1V31.sourceSpin48VectorAction_clifford_generator s v
    rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct] at h
    change
      CliffordAlgebra.ι Q
        (FCP.BFSSS1V31.sourceSpin48VectorAction s v) =
        (s : C) * CliffordAlgebra.ι Q v * star (s : C) at h
    exact h
  constructor
  · intro h v
    have hc :
        CliffordAlgebra.ι Q v =
          (s : C) * CliffordAlgebra.ι Q v * star (s : C) := by
      calc
        CliffordAlgebra.ι Q v =
          CliffordAlgebra.ι Q
            (FCP.BFSSS1V31.sourceSpin48VectorAction s v) := by rw [h v]
        _ = _ := hsrc v
    have hc' := congrArg (fun x : C => x * (s : C)) hc
    simpa only [mul_assoc, hstar, mul_one] using hc'.symm
  · intro h v
    apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
    rw [hsrc v]
    rw [h v, mul_assoc, hunit, mul_one]
#print axioms originalSourceSpin48_trivialAction_iff_generator_commutes

end
end FCP.BFSSS1V52K1A
