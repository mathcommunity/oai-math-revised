import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7OOriginalSourceSOEuclideanSpinPairImageBridgeProbe

/-!
K1D18V7P — exact genuine original sourceSO group transport
into native same-48-label Euclidean isometries.

Accepted V7O shows the CHOSEN original Q-isometry witness
of V7D gives the actual sourceSO GL48 action under the same
source-coordinate linear equivalence E. Although the original
V7D transport uses Classical.choose, its chosen action is
EXACT; this permits proof of the identity and multiplication
laws from the already accepted original sourceSO group.

First establish F(1)=1 and F(g*h)=F(g)*F(h) by pointwise
transport (with exact original group order), then package
the original F as a genuine MonoidHom. No abstract surrogate
sourceSO, no unproved hom premise, no coordinate permutation,
and no weakening of the source-Clifford isometry.

The group hom is a necessary bridge for transporting arbitrary
products of original Spin unit pairs. This gate DOES NOT show
that an arbitrary sourceSO element has such a spin word,
generation, unconditional surjectivity, covering, global Spin9
or BFSS spectral existence.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7P
noncomputable section
open FCP.BFSSS1V0

private abbrev GL48 := Source48Vector ≃ₗ[ℝ] Source48Vector
private abbrev SourceSO :=
  FCP.BFSSS1V52K1D18R.source48SpecialOrthogonalWitnessGL
private abbrev Euc48 := EuclideanSpace ℝ Source48Label
private abbrev E : Source48Vector ≃ₗ[ℝ] Euc48 :=
  FCP.BFSSS1V52K1D18V7C.originalSource48ToEuclidean
private abbrev F (g : SourceSO) : Euc48 ≃ₗᵢ[ℝ] Euc48 :=
  FCP.BFSSS1V52K1D18V7D.sourceSO_toEuclideanIsometry g

/-- Even though V7D chooses a quadratic-isometry witness,
the accepted V7O exact original-source action forces its
transport to preserve the actual sourceSO identity. -/
theorem originalSourceSO_toEuclidean_one :
    F (1 : SourceSO) = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  have h :=
    FCP.BFSSS1V52K1D18V7O.originalSourceSO_toEuclideanIsometry_exactAction
      (1 : SourceSO) (E.symm x)
  calc
    F (1 : SourceSO) x =
        E (((1 : SourceSO) : GL48) (E.symm x)) := by
          simpa only [E.apply_symm_apply] using h
    _ = E (E.symm x) := by rfl
    _ = x := E.apply_symm_apply x

/-- V7D's actual same-label Euclidean transport respects the
ORIGINAL sourceSO group multiplication. Its proof works on
each original vector and explicitly respects g*h order. -/
theorem originalSourceSO_toEuclidean_mul
    (g h : SourceSO) :
    F (g * h) = F g * F h := by
  apply LinearIsometryEquiv.ext
  intro x
  have hmul :=
    FCP.BFSSS1V52K1D18V7O.originalSourceSO_toEuclideanIsometry_exactAction
      (g * h) (E.symm x)
  have hg :=
    FCP.BFSSS1V52K1D18V7O.originalSourceSO_toEuclideanIsometry_exactAction
      g ((h : GL48) (E.symm x))
  have hh :=
    FCP.BFSSS1V52K1D18V7O.originalSourceSO_toEuclideanIsometry_exactAction
      h (E.symm x)
  have hhx : F h x = E ((h : GL48) (E.symm x)) := by
    simpa only [E.apply_symm_apply] using hh
  calc
    F (g * h) x =
        E (((g * h : SourceSO) : GL48) (E.symm x)) := by
          simpa only [E.apply_symm_apply] using hmul
    _ = E ((g : GL48) ((h : GL48) (E.symm x))) := by rfl
    _ = F g (E ((h : GL48) (E.symm x))) := hg.symm
    _ = F g (F h x) := by rw [hhx]
    _ = (F g * F h) x := by rfl

/-- The EXACT accepted original sourceSO subgroup now carries
its actual Euclidean transport as a group-compatible map,
without changing either source action or sourceSO codomain. -/
noncomputable def originalSourceSO_toEuclideanHom :
    SourceSO →* (Euc48 ≃ₗᵢ[ℝ] Euc48) where
  toFun := F
  map_one' := originalSourceSO_toEuclidean_one
  map_mul' := originalSourceSO_toEuclidean_mul

#print axioms originalSourceSO_toEuclidean_one
#print axioms originalSourceSO_toEuclidean_mul
#print axioms originalSourceSO_toEuclideanHom

end
end FCP.BFSSS1V52K1D18V7P
