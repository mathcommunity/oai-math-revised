import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9D6OriginalNativeSixteenSpin48SourceAxisActionProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9D8OriginalFockMajorana48SourceBasisMulVecProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V48OriginalGaugeSpin48ProjectionFiberProbe
import Mathlib.LinearAlgebra.Pi

/-!
S1V52L9D9 — STAGED ONLY, NOT YET KERNEL VERIFIED.
Universal *actual original BFSS SU2* source 48-real Spin(48)
projection. It combines previously accepted L9D6's genuinely
canonical ordered sixteen-block Spin48 action with the actual
source Fock 48-real Majorana mulVec basis action targeted by
L9D8, which remains unqualified at the time of staging.

A pair of genuine REAL-linear endomorphisms of the SAME original
Source48Vector = (Fin24 × Fin2) → ℝ is determined by its
Pi.single coordinate actions (pinned Mathlib LinearMap.pi_ext).
The sourceBlockColorEquiv surjects onto every original 48-real
label. This avoids expanding full 48×48 matrices or replacing
the native Majorana gauge representation.

NO continuity, topological covering, Hilbert/Fock implementer,
charge/Hamiltonian equality or spectral claim is inferred.
NO strict CI until prerequisite L9D8 source-basis mulVec is accepted.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace FCP.BFSSS1V52L9D9
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L8E
open FCP.BFSSS1V52L9D6
open FCP.BFSSS1V52L9D8
open FCP.BFSSSU2PhysicalDomainS1J

/-- For *every* native SU2 gauge element, the previously
constructed ORIGINAL sixteen-factor group homomorphism into
the GENUINE Spin(48) has the exact original Fock 48-real
Majorana matrix as its real-vector projection. -/
theorem originalNativeSixteenSpinHom_coversActualGauge
    (g : GaugeGroup 2) :
    FCP.BFSSS1V48.sourceSpin48CoversActualGauge
      g (originalNativeSixteenSpinHom g) := by
  let spinAction : Source48Vector →ₗ[ℝ] Source48Vector :=
    { toFun := fun v =>
        FCP.BFSSS1V31.sourceSpin48VectorAction
          (originalNativeSixteenSpinHom g) v
      map_add' := by
        intro x y
        exact FCP.BFSSS1V31.sourceSpin48VectorAction_add
          (originalNativeSixteenSpinHom g) x y
      map_smul' := by
        intro a v
        exact FCP.BFSSS1V32.sourceSpin48VectorAction_smul
          (originalNativeSixteenSpinHom g) a v }
  let fockAction : Source48Vector →ₗ[ℝ] Source48Vector :=
    { toFun := fun v => (sourceRealMajoranaMatrix g).mulVec v
      map_add' := by
        intro x y
        exact Matrix.mulVec_add (sourceRealMajoranaMatrix g) x y
      map_smul' := by
        intro a v
        exact Matrix.mulVec_smul (sourceRealMajoranaMatrix g) a v }
  have hlinear : spinAction = fockAction := by
    apply LinearMap.pi_ext
    intro k x
    obtain ⟨⟨α, A⟩, rfl⟩ :=
      sourceBlockColorEquiv.surjective k
    have hsingle :
        (Pi.single (sourceBlockColorLabel α A) x : Source48Vector) =
          x • sourceBlockColorAxis α A := by
      ext j
      by_cases hj : j = sourceBlockColorLabel α A <;>
        simp [sourceBlockColorAxis, hj]
    -- The displayed Pi.single uses the original source equivalence,
    -- whereas hsingle uses sourceBlockColorLabel, its definitionally
    -- equal name. Expose the SAME original label on both sides before
    -- asking rw to match; no physical or index conversion is changed.
    change spinAction (Pi.single (sourceBlockColorLabel α A) x) =
      fockAction (Pi.single (sourceBlockColorLabel α A) x)
    rw [hsingle, map_smul, map_smul]
    change x • FCP.BFSSS1V31.sourceSpin48VectorAction
      (originalNativeSixteenSpinHom g) (sourceBlockColorAxis α A) =
      x • (sourceRealMajoranaMatrix g).mulVec
        (sourceBlockColorAxis α A)
    exact congrArg (fun v : Source48Vector => x • v)
      ((originalNativeSixteenSpinHom_sourceAxis_action g α A).trans
        (originalSourceRealMajoranaMatrix_mulVec_sourceAxis g α A).symm)
  intro v
  exact LinearMap.congr_fun hlinear v

#print axioms originalNativeSixteenSpinHom_coversActualGauge

end
end FCP.BFSSS1V52L9D9
