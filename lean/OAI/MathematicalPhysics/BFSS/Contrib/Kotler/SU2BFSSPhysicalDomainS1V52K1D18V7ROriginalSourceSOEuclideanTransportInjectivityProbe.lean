import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7QOriginalSourceEvenUnitListSpinWordImageProbe

/-!
K1D18V7R — exact original sourceSO-to-Euclidean injectivity,
without hypothesizing SO generation or original Spin surjectivity.

V7O accepted: the actual V7D sourceSO transport uses a CHOSEN
original-Q isometry witness but its action is exactly the
unchanged original sourceSO GL48 action under the canonical
same-48-label linear equivalence E. E is invertible.
V7P accepted: the exact same map is a genuine MonoidHom.
V7Q accepted: any even list of native unit-normal hyperplane
reflections has an ACTUAL original Clifford Spin image word.

Here only prove equality reflection back from the E-transport
to the original sourceSO GL48 action and injectivity of the
existing MonoidHom. NO substitute source SO, quadratic form,
original-label permutation, Spin-word generation assumption,
or new surjectivity hypothesis is introduced.

Source Spin surjectivity is a distinct next theorem, requiring
V7L, V7Q and this bridge. Topological covering, global Spin9
lift and BFSS spectral existence remain separate obligations.
All roots CANDIDATE pending full source-exact strict CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7R
noncomputable section
open FCP.BFSSS1V0

private abbrev GL48 := Source48Vector ≃ₗ[ℝ] Source48Vector
private abbrev SourceSO :=
  FCP.BFSSS1V52K1D18R.source48SpecialOrthogonalWitnessGL
private abbrev Euc48 := EuclideanSpace ℝ Source48Label
private abbrev E : Source48Vector ≃ₗ[ℝ] Euc48 :=
  FCP.BFSSS1V52K1D18V7C.originalSource48ToEuclidean

/-- The ACTUAL original sourceSO transport is injective because
pointwise equality on the native Euclidean target implies
equality of the underlying ORIGINAL 48-label source GL actions.
This uses V7O's original-action bridge, not an assumption of
faithfulness, surjectivity or an invented orthogonal model. -/
theorem originalSourceSO_toEuclideanIsometry_injective :
    Function.Injective
      (FCP.BFSSS1V52K1D18V7D.sourceSO_toEuclideanIsometry :
        SourceSO → Euc48 ≃ₗᵢ[ℝ] Euc48) := by
  intro g h hgh
  apply Subtype.ext
  apply LinearEquiv.ext
  intro w
  have hpoint :
      FCP.BFSSS1V52K1D18V7D.sourceSO_toEuclideanIsometry g (E w) =
        FCP.BFSSS1V52K1D18V7D.sourceSO_toEuclideanIsometry h (E w) :=
    congrArg (fun f : Euc48 ≃ₗᵢ[ℝ] Euc48 => f (E w)) hgh
  rw [FCP.BFSSS1V52K1D18V7O.originalSourceSO_toEuclideanIsometry_exactAction g w,
    FCP.BFSSS1V52K1D18V7O.originalSourceSO_toEuclideanIsometry_exactAction h w] at hpoint
  exact E.injective hpoint

/-- The already-qualified V7P group homomorphism is injective;
there is no loss of information through the original source-Q
witness choice or the same-label Euclidean coordinate transport. -/
theorem originalSourceSO_toEuclideanHom_injective :
    Function.Injective
      FCP.BFSSS1V52K1D18V7P.originalSourceSO_toEuclideanHom := by
  change Function.Injective
    (FCP.BFSSS1V52K1D18V7D.sourceSO_toEuclideanIsometry :
      SourceSO → Euc48 ≃ₗᵢ[ℝ] Euc48)
  exact originalSourceSO_toEuclideanIsometry_injective

#print axioms originalSourceSO_toEuclideanIsometry_injective
#print axioms originalSourceSO_toEuclideanHom_injective

end
end FCP.BFSSS1V52K1D18V7R
