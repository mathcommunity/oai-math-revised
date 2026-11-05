import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18EOriginalSpinTwoFactorDeterminantProbe

/-!
K1D18F — exact original 48-real vector action of ALL actual
Lipschitz-group units, via pinned Mathlib subgroup-closure preservation.

No alternative group, vector space, Clifford generator, or quadratic
form. The unit is an actual member of lipschitzGroup Q, which is the
pinned Subgroup.closure of invertible original Clifford generators.
This proves only existence, uniqueness, compatibility with Clifford
conjugation and real linearity. Spin restriction, group multiplication,
determinant, parity and SO48 remain separate obligations.

CANDIDATE until fresh strict source- and axiom-qualified compiler CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18F
noncomputable section

open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Every actual source Lipschitz unit sends any original real
48-dimensional Clifford generator to a UNIQUE original source vector. -/
theorem sourceLipschitz_conjugated_generator_unique
    (u : Cˣ) (hu : u ∈ lipschitzGroup Q)
    (v : Source48Vector) :
    ∃! w : Source48Vector,
      CliffordAlgebra.ι Q w =
        ConjAct.toConjAct u • (CliffordAlgebra.ι Q v) := by
  obtain ⟨w, hw⟩ :=
    lipschitzGroup.conjAct_smul_ι_mem_range_ι hu v
  refine ⟨w, hw, ?_⟩
  intro y hy
  exact FCP.BFSSS1V30.source48_cliffordGenerator_injective
    (hy.trans hw.symm)

/-- The unique original source vector associated to conjugation by
an actual Lipschitz-subgroup Clifford unit. The membership proof is
used only to establish uniqueness, not to change the representation. -/
noncomputable def sourceLipschitzVectorAction
    (u : Cˣ) (hu : u ∈ lipschitzGroup Q)
    (v : Source48Vector) : Source48Vector :=
  Classical.choose
    (sourceLipschitz_conjugated_generator_unique u hu v).exists

theorem sourceLipschitzVectorAction_clifford_generator
    (u : Cˣ) (hu : u ∈ lipschitzGroup Q)
    (v : Source48Vector) :
    CliffordAlgebra.ι Q (sourceLipschitzVectorAction u hu v) =
      ConjAct.toConjAct u • (CliffordAlgebra.ι Q v) := by
  exact Classical.choose_spec
    (sourceLipschitz_conjugated_generator_unique u hu v).exists

/-- Additivity of the ACTUAL source Lipschitz vector action, using
the original degree-one Clifford embedding and conjugation action. -/
theorem sourceLipschitzVectorAction_add
    (u : Cˣ) (hu : u ∈ lipschitzGroup Q)
    (v w : Source48Vector) :
    sourceLipschitzVectorAction u hu (v + w) =
      sourceLipschitzVectorAction u hu v +
        sourceLipschitzVectorAction u hu w := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q (sourceLipschitzVectorAction u hu (v + w)) =
        ConjAct.toConjAct u • CliffordAlgebra.ι Q (v + w) :=
      sourceLipschitzVectorAction_clifford_generator u hu (v + w)
    _ = (ConjAct.toConjAct u • CliffordAlgebra.ι Q v) +
        (ConjAct.toConjAct u • CliffordAlgebra.ι Q w) := by
      rw [map_add, smul_add]
    _ = CliffordAlgebra.ι Q
        (sourceLipschitzVectorAction u hu v +
          sourceLipschitzVectorAction u hu w) := by
      rw [map_add, sourceLipschitzVectorAction_clifford_generator,
        sourceLipschitzVectorAction_clifford_generator]

/-- Real scalar-linearity of the ACTUAL source Lipschitz vector action;
no guessed orthogonal action and no determinant claim. -/
theorem sourceLipschitzVectorAction_smul
    (u : Cˣ) (hu : u ∈ lipschitzGroup Q)
    (r : ℝ) (v : Source48Vector) :
    sourceLipschitzVectorAction u hu (r • v) =
      r • sourceLipschitzVectorAction u hu v := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q (sourceLipschitzVectorAction u hu (r • v)) =
        ConjAct.toConjAct u • CliffordAlgebra.ι Q (r • v) :=
      sourceLipschitzVectorAction_clifford_generator u hu (r • v)
    _ = r • (ConjAct.toConjAct u • CliffordAlgebra.ι Q v) := by
      rw [map_smul]
      exact (smul_comm r (ConjAct.toConjAct u)
        (CliffordAlgebra.ι Q v)).symm
    _ = CliffordAlgebra.ι Q
        (r • sourceLipschitzVectorAction u hu v) := by
      rw [map_smul, sourceLipschitzVectorAction_clifford_generator]

#print axioms sourceLipschitz_conjugated_generator_unique
#print axioms sourceLipschitzVectorAction_clifford_generator
#print axioms sourceLipschitzVectorAction_add
#print axioms sourceLipschitzVectorAction_smul

end
end FCP.BFSSS1V52K1D18F
