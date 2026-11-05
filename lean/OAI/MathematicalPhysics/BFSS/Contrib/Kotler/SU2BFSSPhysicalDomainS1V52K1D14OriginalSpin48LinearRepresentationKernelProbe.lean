import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D13OriginalSpin48LinearRepresentationProbe

/-!
K1D14 — the exact kernel of the newly accepted original source Spin48
real-linear representation, not just a previously established
pointwise-fixer set. K1D13 now supplies the real monoid homomorphism.

Compose the qualified K1D11 exact pointwise two-sign theorem with
K1D13's actual Spin48 →* GL(Source48Vector) group-homomorphism.
The resulting kernel statement concerns the genuine Mathlib
MonoidHom.ker subgroup. Explicitly retain distinctness of the signs.

NO assertion that the image lands in the source orthogonal or
special orthogonal groups, no surjectivity, covering, global Spin9,
or BFSS spectral existence. CANDIDATE until independent strict CI.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace FCP.BFSSS1V52K1D14
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- The genuine original Spin48 GL representation maps a group
element to the identity real-linear automorphism precisely for the
two actual Spin elements in K1D11. -/
theorem originalSourceSpin48LinearRepresentation_eq_one_iff_two_signs
    (s : spinGroup Q) :
    FCP.BFSSS1V52K1D13.originalSourceSpin48LinearRepresentation s = 1 ↔
      s = 1 ∨ s = FCP.BFSSS1V52K1D11.originalSourceNegativeCentral := by
  constructor
  · intro h
    apply (FCP.BFSSS1V52K1D11.originalSourceSpin48_trivialAction_iff_two_signs s).mp
    intro v
    have hv := congrArg
      (fun f : Source48Vector ≃ₗ[ℝ] Source48Vector => f v) h
    exact hv
  · intro hs
    apply LinearEquiv.ext
    intro v
    exact (FCP.BFSSS1V52K1D11.originalSourceSpin48_trivialAction_iff_two_signs s).mpr hs v

/-- The *actual* MonoidHom kernel subgroup of the source Spin48 → GL48
homomorphism, viewed as a set, consists of exactly the two genuine
Spin-group elements. This is stronger than an unbundled pointwise
stabilizer statement. -/
theorem originalSourceSpin48LinearRepresentation_ker_eq_two_sign_set :
    ((FCP.BFSSS1V52K1D13.originalSourceSpin48LinearRepresentation).ker :
        Set (spinGroup Q)) =
      ({1, FCP.BFSSS1V52K1D11.originalSourceNegativeCentral} :
        Set (spinGroup Q)) := by
  ext s
  simpa only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff,
    Set.mem_singleton_iff] using
    (originalSourceSpin48LinearRepresentation_eq_one_iff_two_signs s)

/-- The original source Spin48 representation is not injective,
because both the identity and the distinct negative central group
element belong to its actual homomorphism kernel. -/
theorem originalSourceSpin48LinearRepresentation_not_injective :
    ¬ Function.Injective
      FCP.BFSSS1V52K1D13.originalSourceSpin48LinearRepresentation := by
  intro hinj
  have hneg :
      FCP.BFSSS1V52K1D13.originalSourceSpin48LinearRepresentation
        FCP.BFSSS1V52K1D11.originalSourceNegativeCentral = 1 :=
    (originalSourceSpin48LinearRepresentation_eq_one_iff_two_signs
      FCP.BFSSS1V52K1D11.originalSourceNegativeCentral).mpr (Or.inr rfl)
  have hmap :
      FCP.BFSSS1V52K1D13.originalSourceSpin48LinearRepresentation
        FCP.BFSSS1V52K1D11.originalSourceNegativeCentral =
      FCP.BFSSS1V52K1D13.originalSourceSpin48LinearRepresentation 1 := by
    simpa only [map_one] using hneg
  have hsign :
      FCP.BFSSS1V52K1D11.originalSourceNegativeCentral = (1 : spinGroup Q) :=
    hinj hmap
  exact FCP.BFSSS1V52K1D11.originalSourceSpin48_one_ne_negativeCentral
    hsign.symm

#print axioms originalSourceSpin48LinearRepresentation_eq_one_iff_two_signs
#print axioms originalSourceSpin48LinearRepresentation_ker_eq_two_sign_set
#print axioms originalSourceSpin48LinearRepresentation_not_injective

end
end FCP.BFSSS1V52K1D14
