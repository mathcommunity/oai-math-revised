import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentCliffordIntertwining
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentMajoranaAction
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52M3JIndependentUnitaryExistenceProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5C1OriginalFockCliffordAlgebraUniversalLiftProbe
import Mathlib.Algebra.Algebra.Tower

/-!
SOURCE-EXACT RESEARCH CANDIDATE -- NOT LOCALLY TYPECHECKED.
The actual original-source OAI/M3J .oleans are unavailable locally.
No surrogate source modules or declarations have been substituted.

Proposed smallest strict target: independent_original_clifford_intertwining.
The independent action is the universal Clifford action of the input theta;
it is defined before, and without, J. The source action is the accepted
originalFockCliffordAlgHom, converted from continuous to algebraic endomorphisms.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.IndependentOriginalCliffordBridge
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSS1V0 FCP.BFSSS1V5
open FCP.BFSSS1V52L9E2 FCP.BFSSS1V52L9E4 FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52M3JIndependent
open FCP.IndependentM3JAction FCP.IndependentMajoranaAction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

def originalLabelledTheta
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (p : SourceLabel) : Module.End ℂ E :=
  theta (sourceToManuscriptLabel p).1 (sourceToManuscriptLabel p).2

variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
  theta α A * theta β B + theta β B * theta α A =
    (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))

include hCAR in
theorem originalLabelledTheta_CAR (p q : SourceLabel) :
    originalLabelledTheta theta p * originalLabelledTheta theta q +
      originalLabelledTheta theta q * originalLabelledTheta theta p =
        (if p = q then (1 : ℂ) else 0) • (1 : Module.End ℂ E) := by
  let e := sourceToManuscriptLabel
  have heq : ((e p).1 = (e q).1 ∧ (e p).2 = (e q).2) ↔ p = q := by
    constructor
    · rintro ⟨h1, h2⟩
      exact e.injective (Prod.ext h1 h2)
    · intro h
      subst q
      exact ⟨rfl, rfl⟩
  change theta (e p).1 (e p).2 * theta (e q).1 (e q).2 +
      theta (e q).1 (e q).2 * theta (e p).1 (e p).2 =
        (if p = q then (1 : ℂ) else 0) • (1 : Module.End ℂ E)
  simpa only [heq] using
    hCAR (e p).1 (e q).1 (e p).2 (e q).2

/-- Independently CONSTRUCTED original real Clifford action, with the exact
accepted coordinate relabeling and positive sqrt(2) normalization. -/
def independentOriginalClifford : C →ₐ[ℝ] Module.End ℂ E :=
  cliffordAction (originalLabelledTheta theta)
    (originalLabelledTheta_CAR theta hCAR)

def independentOriginalSpinHom [FiniteDimensional ℂ E]
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    spinGroup Q →* (E ≃ₗᵢ[ℂ] E) :=
  majoranaSpinHom (originalLabelledTheta theta)
    (originalLabelledTheta_CAR theta hCAR)
    (fun p => hHermitian (sourceToManuscriptLabel p).1
      (sourceToManuscriptLabel p).2)

/-- This is exactly the accepted original Fock real Clifford action, with
only the continuous-linear/algebraic-endomorphism interface changed. -/
def sourceCliffordEnd : C →ₐ[ℝ] Module.End ℂ (Fermion 2) :=
  (((Module.End.toContinuousLinearMap (Fermion 2)).symm).restrictScalars ℝ).toAlgHom.comp
    originalFockCliffordAlgHom

/-- The exact coordinate-axis interface for the compiled generic extension.
The source side uses C1 and L9E4's already accepted axis lemmas. -/
theorem independent_original_axis_intertwining
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (p : SourceLabel) (w : E) :
    J (independentOriginalClifford theta hCAR
      (CliffordAlgebra.ι Q (Pi.single p (1 : ℝ))) w) =
      sourceCliffordEnd (CliffordAlgebra.ι Q (Pi.single p (1 : ℝ))) (J w) := by
  let q := sourceBlockColorEquiv.symm p
  let v : Source48Vector := sourceBlockColorAxis q.1 q.2
  have hv : v = Pi.single p (1 : ℝ) := by
    dsimp only [v, sourceBlockColorAxis, sourceBlockColorLabel, q]
    rw [sourceBlockColorEquiv.apply_symm_apply]
  have hsource : originalFockCliffordAlgHom
      (CliffordAlgebra.ι Q (Pi.single p (1 : ℝ))) =
        originalNormalizedFockMajorana q.1 q.2 := by
    rw [← hv, originalFockCliffordAlgHom_generator]
    exact originalFockGammaRealLinear_sourceAxis q.1 q.2
  change J (cliffordAction (originalLabelledTheta theta)
      (originalLabelledTheta_CAR theta hCAR)
      (CliffordAlgebra.ι Q (Pi.single p (1 : ℝ))) w) =
    originalFockCliffordAlgHom (CliffordAlgebra.ι Q (Pi.single p (1 : ℝ))) (J w)
  have haxis :
      cliffordAction (originalLabelledTheta theta)
        (originalLabelledTheta_CAR theta hCAR)
        (CliffordAlgebra.ι Q (Pi.single p (1 : ℝ))) =
          (Real.sqrt 2 : ℂ) • originalLabelledTheta theta p := by
    -- S1V0's Q and the generic coordinateQuadratic have identical
    -- unit weights and source labels, but rw uses insufficient transparency.
    change cliffordAction (originalLabelledTheta theta)
      (originalLabelledTheta_CAR theta hCAR)
      (CliffordAlgebra.ι (coordinateQuadratic (R := ℝ) (I := SourceLabel))
        (Pi.single p (1 : ℝ))) = _
    exact cliffordAction_axis _ _ p
  rw [haxis, hsource]
  change J ((Real.sqrt 2 : ℂ) •
      theta (sourceToManuscriptLabel p).1 (sourceToManuscriptLabel p).2 w) =
    (Real.sqrt 2 : ℂ) • pairedTheta (spinPairEquiv.symm q.1) q.2 (J w)
  rw [map_smul, hJ]
  rfl

/-- Proposed first source-exact strict gate: the actual M3J generator
intertwiner extends to EVERY original real Clifford element. -/
theorem independent_original_clifford_intertwining
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (x : C) (w : E) :
    J (independentOriginalClifford theta hCAR x w) =
      originalFockCliffordAlgHom x (J w) := by
  exact FCP.IndependentCliffordIntertwining.intertwines_all_of_coordinate_axes
    Q (independentOriginalClifford theta hCAR) sourceCliffordEnd J.toLinearMap
    (independent_original_axis_intertwining theta hCAR J hJ) x w

#print axioms independentOriginalClifford
#print axioms independentOriginalSpinHom
#print axioms independent_original_axis_intertwining
#print axioms independent_original_clifford_intertwining

end
end FCP.IndependentOriginalCliffordBridge
