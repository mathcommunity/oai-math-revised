import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18FOriginalLipschitzVectorActionProbe

/-!
K1D18G — original 48-real Lipschitz subgroup action laws, a
real-linear source map, and restriction to the already accepted
genuine original S1V31 Spin(48) vector action.

Genuinely uses lipschitzGroup source48Quadratic as defined by the
pinned Mathlib Subgroup.closure, not a postulated free word group.
No parity/determinant theorem, universal factorization, SO48,
covering, Spin9 global lift, or BFSS spectral result is claimed.

Candidate until exact owner source/axiom strict CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18G
noncomputable section

open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Mathlib's actual source Spin(48) unit belongs to its actual
source Lipschitz subgroup, not merely to a surrogate unit group. -/
theorem originalSourceSpin48_unit_mem_lipschitz
    (s : spinGroup Q) :
    spinGroup.toUnits s ∈ lipschitzGroup Q := by
  have hs : ((spinGroup.toUnits s : Cˣ) : C) ∈ spinGroup Q := by
    change (s : C) ∈ spinGroup Q
    exact s.property
  exact spinGroup.units_mem_lipschitzGroup hs

/-- The actual source Lipschitz unit identity fixes every original
48-real source vector, proved through the injective source Clifford
generator rather than a replacement action. -/
theorem sourceLipschitzVectorAction_one (v : Source48Vector) :
    FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction
      (1 : Cˣ) (lipschitzGroup Q).one_mem v = v := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  rw [FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction_clifford_generator]
  simp

/-- The actual source Lipschitz vector action composes in the same
order as multiplication of actual source Clifford units. -/
theorem sourceLipschitzVectorAction_mul
    (u v : Cˣ) (hu : u ∈ lipschitzGroup Q)
    (hv : v ∈ lipschitzGroup Q) (w : Source48Vector) :
    FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction
      (u * v) ((lipschitzGroup Q).mul_mem hu hv) w =
    FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction u hu
      (FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction v hv w) := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q
      (FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction
        (u * v) ((lipschitzGroup Q).mul_mem hu hv) w) =
      ConjAct.toConjAct (u * v) • CliffordAlgebra.ι Q w :=
      FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction_clifford_generator
        (u * v) ((lipschitzGroup Q).mul_mem hu hv) w
    _ = ConjAct.toConjAct u •
        (ConjAct.toConjAct v • CliffordAlgebra.ι Q w) := by
      rw [map_mul, mul_smul]
    _ = CliffordAlgebra.ι Q
      (FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction u hu
        (FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction v hv w)) := by
      rw [FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction_clifford_generator,
        FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction_clifford_generator]

/-- The exact original S1V31 source Spin48 action IS the restriction
of the newly constructed actual Lipschitz subgroup source action. -/
theorem sourceLipschitzVectorAction_agrees_originalSpin48
    (s : spinGroup Q) (v : Source48Vector) :
    FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction
      (spinGroup.toUnits s)
      (originalSourceSpin48_unit_mem_lipschitz s) v =
    FCP.BFSSS1V31.sourceSpin48VectorAction s v := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q
      (FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction
        (spinGroup.toUnits s)
        (originalSourceSpin48_unit_mem_lipschitz s) v) =
      ConjAct.toConjAct (spinGroup.toUnits s) • CliffordAlgebra.ι Q v :=
      FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction_clifford_generator
        (spinGroup.toUnits s) (originalSourceSpin48_unit_mem_lipschitz s) v
    _ = CliffordAlgebra.ι Q
      (FCP.BFSSS1V31.sourceSpin48VectorAction s v) :=
      (FCP.BFSSS1V31.sourceSpin48VectorAction_clifford_generator s v).symm

/-- The source Lipschitz action is a REAL-LINEAR ENDOMORPHISM of
the ORIGINAL 48-real source module, not an assumed SO48 element. -/
noncomputable def originalSourceLipschitzLinearMap
    (u : Cˣ) (hu : u ∈ lipschitzGroup Q) :
    Source48Vector →ₗ[ℝ] Source48Vector where
  toFun := FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction u hu
  map_add' := FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction_add u hu
  map_smul' := FCP.BFSSS1V52K1D18F.sourceLipschitzVectorAction_smul u hu

#print axioms originalSourceSpin48_unit_mem_lipschitz
#print axioms sourceLipschitzVectorAction_one
#print axioms sourceLipschitzVectorAction_mul
#print axioms sourceLipschitzVectorAction_agrees_originalSpin48
#print axioms originalSourceLipschitzLinearMap

end
end FCP.BFSSS1V52K1D18G
