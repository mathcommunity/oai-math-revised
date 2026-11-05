import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AIOriginalFullL2ParityLiftProbe

/-!
# H5E8AJ — the genuine original BFSS FullL2 parity unitary

The pinned Mathlib Lp composition laws make the accepted AI
linear isometry involutive, hence SURJECTIVE. Only now may we package
it as a genuine complex-linear isometry equivalence (unitary).

This is an exact Hilbert-space result for original Boson/Fermion/Lp;
its physical SU(2) gauge invariance and closed source Hamiltonian
conjugation remain distinct future proof obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AJ
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2PhysicalDomainL6H5E8AI
open MeasureTheory

/-- Apply exact source Lp parity twice and get back the original
Hilbert vector, without choosing representatives of Lp classes. -/
theorem originalFullL2Parity_involutive {N : ℕ} (g : FullL2 N) :
    originalFullL2Parity (originalFullL2Parity g) = g := by
  let inv : Boson N → Boson N := fun x => -x
  let h : MeasurePreserving inv
      (volume : Measure (Boson N)) (volume : Measure (Boson N)) :=
    originalBosonNeg_measurePreserving
  change Lp.compMeasurePreserving inv h
    (Lp.compMeasurePreserving inv h g) = g
  rw [← Lp.compMeasurePreserving_comp_apply g h h]
  have hinv : inv ∘ inv = id := by
    funext x
    simp [inv]
  -- Avoid dependent rewriting of the measure-preservation proof:
  -- identify the two Lp representatives almost everywhere.
  apply Lp.ext
  have hcoe :=
    Lp.coeFn_compMeasurePreserving g (h.comp h)
  filter_upwards [hcoe] with x hx
  simpa only [hinv, Function.comp_apply, id_eq] using hx

/-- Genuine surjective complex-linear isometric equivalence of the
original BFSS FullL2, not a newly assumed Hilbert-space symmetry. -/
noncomputable def originalFullL2ParityUnitary {N : ℕ} :
    FullL2 N ≃ₗᵢ[ℂ] FullL2 N :=
  LinearIsometryEquiv.ofSurjective (originalFullL2Parity (N := N))
    (by
      intro g
      exact ⟨originalFullL2Parity g,
        originalFullL2Parity_involutive g⟩)

theorem originalFullL2ParityUnitary_apply {N : ℕ} (g : FullL2 N) :
    originalFullL2ParityUnitary g = originalFullL2Parity g := by
  rfl

theorem originalFullL2ParityUnitary_sq {N : ℕ} (g : FullL2 N) :
    originalFullL2ParityUnitary
      (originalFullL2ParityUnitary g) = g := by
  change originalFullL2Parity (originalFullL2Parity g) = g
  exact originalFullL2Parity_involutive g

theorem originalFullL2ParityUnitary_coreToL2 {N : ℕ}
    (f : SmoothCore N) :
    originalFullL2ParityUnitary (OAI.BFSSQuantum.AlgebraData.coreToL2 f) =
      OAI.BFSSQuantum.AlgebraData.coreToL2
        (FCP.BFSSSU2PhysicalDomainL6H5E8AF.originalSmoothParity f) := by
  exact originalFullL2Parity_coreToL2 f

#print axioms originalFullL2Parity_involutive
#print axioms originalFullL2ParityUnitary
#print axioms originalFullL2ParityUnitary_apply
#print axioms originalFullL2ParityUnitary_sq
#print axioms originalFullL2ParityUnitary_coreToL2

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AJ
