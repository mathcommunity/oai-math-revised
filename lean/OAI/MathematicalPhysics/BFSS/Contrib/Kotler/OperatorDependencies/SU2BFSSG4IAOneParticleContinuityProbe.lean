import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4HExactThetaCovarianceProbe

/-!
# BFSS SU(2) G4-I-A — parameter continuity of genuine one-particle color action

From the actual pinned `pairedAlgebraData.adjointCoefficient` trace
formula, show that each genuine SU(2) color rotation entry varies
continuously with the group element. Transport continuity through the
already accepted eight-color-block and `colorModeEquiv` indexing to
the ACTUAL G3-C complex 24-mode one-particle matrix.

This is only the first bounded prerequisite for the pinned
`GaugeData.fermion_continuous` joint Fock-space action.
We do NOT infer Fock continuity from isometry or group laws alone.
-/

namespace FCP.BFSSSU2GaugeG4IA
noncomputable section

open Matrix
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG3A FCP.BFSSSU2GaugeG3C

/-- The exact source-defined coefficient, not an arbitrary continuous
three-color representation. This relies on matrix multiplication,
conjugate-transposition, finite trace and real-part continuity. -/
theorem adjointColorMatrix_entry_continuous
    (B A : ColorIndex 2) :
    Continuous (fun g : GaugeGroup 2 => adjointColorMatrix g B A) := by
  have hmat : Continuous (fun g : GaugeGroup 2 =>
      pairedAlgebraData.color B *
        ((g : ColorMatrix 2) * pairedAlgebraData.color A *
          (g : ColorMatrix 2)ᴴ)) := by
    exact continuous_const.mul
      ((continuous_subtype_val.mul continuous_const).mul
        continuous_subtype_val.star)
  have htrace : Continuous (fun g : GaugeGroup 2 =>
      Matrix.trace (pairedAlgebraData.color B *
        ((g : ColorMatrix 2) * pairedAlgebraData.color A *
          (g : ColorMatrix 2)ᴴ))) := by
    unfold Matrix.trace
    exact continuous_finsetSum _ (fun i _ => hmat.matrix_elem i i)
  change Continuous (fun g : GaugeGroup 2 =>
    (Matrix.trace (pairedAlgebraData.color B *
      ((g : ColorMatrix 2) * pairedAlgebraData.color A *
        (g : ColorMatrix 2)ᴴ))).re)
  exact Complex.continuous_re.comp htrace

/-- The literal G3-C complex matrix on all 24 Fock orbital modes
depends continuously on the genuine SU(2) group parameter. -/
theorem complexOneParticleMatrix_continuous :
    Continuous (fun g : GaugeGroup 2 => complexOneParticleMatrix g) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro m
  rcases colorModeEquiv.surjective i with ⟨⟨j, B⟩, rfl⟩
  rcases colorModeEquiv.surjective m with ⟨⟨k, A⟩, rfl⟩
  change Continuous (fun g : GaugeGroup 2 =>
    complexOneParticleMatrix g (colorModeEquiv (j,B))
      (colorModeEquiv (k,A)))
  simp_rw [complexOneParticleMatrix_block]
  by_cases h : j = k
  · simp only [_root_.ite_eq_left h]
    exact Complex.continuous_ofReal.comp
      (adjointColorMatrix_entry_continuous B A)
  · simp only [_root_.ite_eq_right h]
    exact continuous_const

#print axioms adjointColorMatrix_entry_continuous
#print axioms complexOneParticleMatrix_continuous

end
end FCP.BFSSSU2GaugeG4IA
