import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18RSourceSpinSpecialOrthogonalWitnessProbe

/-!
K1D18S — package the original K1D13 source Spin48 GL48 action
as a homomorphism into the new R source-Q isometry-witness,
determinant-one subgroup; transport K1D14's actual two-sign kernel.
No alternate source labels, matrix SO identification, surjectivity,
covering, global Spin9, or physical BFSS spectral claim.
Research candidate pending strict Lean compilation and axiom audit.
-/
set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18S
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev GL48 := Source48Vector ≃ₗ[ℝ] Source48Vector
private abbrev SourceSO :=
  FCP.BFSSS1V52K1D18R.source48SpecialOrthogonalWitnessGL

/-- Genuine original source Spin48 representation with its
already-proved determinant-one source-quadratic isometry witness. -/
noncomputable def originalSourceSpin48SpecialOrthogonalWitnessRepresentation :
    spinGroup Q →* SourceSO where
  toFun s :=
    ⟨FCP.BFSSS1V52K1D13.originalSourceSpin48LinearRepresentation s,
      FCP.BFSSS1V52K1D18R.originalSourceSpin48_mem_specialOrthogonalWitness s⟩
  map_one' := by
    apply Subtype.ext
    exact map_one FCP.BFSSS1V52K1D13.originalSourceSpin48LinearRepresentation
  map_mul' s t := by
    apply Subtype.ext
    exact map_mul
      FCP.BFSSS1V52K1D13.originalSourceSpin48LinearRepresentation s t

/-- Forgetting the witness-subgroup codomain gives precisely
the accepted K1D13 real-linear source representation. -/
theorem originalSourceSpin48SpecialOrthogonalWitnessRepresentation_coe
    (s : spinGroup Q) :
    ((originalSourceSpin48SpecialOrthogonalWitnessRepresentation s :
        SourceSO) : GL48) =
      FCP.BFSSS1V52K1D13.originalSourceSpin48LinearRepresentation s := by
  rfl

/-- Equality with the subgroup identity is exactly equality with
the original GL identity; no new kernel classification assumption. -/
theorem originalSourceSpin48SpecialOrthogonalWitnessRepresentation_eq_one_iff_original
    (s : spinGroup Q) :
    originalSourceSpin48SpecialOrthogonalWitnessRepresentation s = 1 ↔
      FCP.BFSSS1V52K1D13.originalSourceSpin48LinearRepresentation s = 1 := by
  constructor
  · intro h
    have hc : ((originalSourceSpin48SpecialOrthogonalWitnessRepresentation s :
          SourceSO) : GL48) = ((1 : SourceSO) : GL48) :=
      congrArg (fun x : SourceSO => (x : GL48)) h
    simpa only [originalSourceSpin48SpecialOrthogonalWitnessRepresentation_coe,
      Subgroup.coe_one] using hc
  · intro h
    apply Subtype.ext
    simpa only [originalSourceSpin48SpecialOrthogonalWitnessRepresentation_coe,
      Subgroup.coe_one] using h

/-- Transport the exact accepted two-sign K1D14 MonoidHom kernel
to this actual original Spin48 → source-quadratic SO subgroup. -/
theorem originalSourceSpin48SpecialOrthogonalWitnessRepresentation_ker_eq_two_sign_set :
    ((originalSourceSpin48SpecialOrthogonalWitnessRepresentation).ker :
        Set (spinGroup Q)) =
      ({1, FCP.BFSSS1V52K1D11.originalSourceNegativeCentral} :
        Set (spinGroup Q)) := by
  ext s
  simpa only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff,
    Set.mem_singleton_iff] using
    ((originalSourceSpin48SpecialOrthogonalWitnessRepresentation_eq_one_iff_original s).trans
      (FCP.BFSSS1V52K1D14.originalSourceSpin48LinearRepresentation_eq_one_iff_two_signs s))

#print axioms originalSourceSpin48SpecialOrthogonalWitnessRepresentation
#print axioms originalSourceSpin48SpecialOrthogonalWitnessRepresentation_coe
#print axioms originalSourceSpin48SpecialOrthogonalWitnessRepresentation_eq_one_iff_original
#print axioms originalSourceSpin48SpecialOrthogonalWitnessRepresentation_ker_eq_two_sign_set

end
end FCP.BFSSS1V52K1D18S
