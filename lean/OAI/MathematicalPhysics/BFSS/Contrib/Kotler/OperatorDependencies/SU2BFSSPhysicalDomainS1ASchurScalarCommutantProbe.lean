import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG1APairedThetaProbe
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# BFSS SU(2) S1A — scalar commutant of the exact paired 48 Majoranas

The first source-to-manuscript Spin(48) representation-matching hinge.
If a complex-linear operator on the original 24-orbital Fermion 2 space
commutes with all 48 accepted paired theta operators, it is scalar.

Uses the pinned Mathlib finite-dimensional algebraically closed field
eigenvalue theorem and the accepted pairedTheta_irreducible certificate.
This is not yet a Spin(48) lift, an SU(2) character theorem, an
intertwiner with an independent representation or a spectral theorem.
-/

namespace FCP.BFSSSU2PhysicalDomainS1A
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A

/-- Exact paired 48-Majorana Schur commutant on Fermion 2.
    The hypothesis is pointwise commutation, avoiding any unproved
    Clifford-algebra module or external spin representation. -/
theorem pairedTheta_commutant_scalar
    (L : Module.End ℂ (Fermion 2))
    (hcomm : ∀ α : SpinIndex, ∀ A : ColorIndex 2, ∀ v : Fermion 2,
      L (pairedTheta α A v) = pairedTheta α A (L v)) :
    ∃ z : ℂ, ∀ v : Fermion 2, L v = z • v := by
  obtain ⟨z, hz⟩ := Module.End.exists_eigenvalue L
  have hstable :
      ∀ α : SpinIndex, ∀ A : ColorIndex 2,
        ∀ v ∈ L.eigenspace z, pairedTheta α A v ∈ L.eigenspace z := by
    intro α A v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    calc
      L (pairedTheta α A v) = pairedTheta α A (L v) := hcomm α A v
      _ = pairedTheta α A (z • v) := by rw [hv]
      _ = z • pairedTheta α A v := map_smul _ _ _
  have htop : L.eigenspace z = ⊤ := by
    rcases pairedTheta_irreducible (L.eigenspace z) hstable with hbot | htop
    · exact (hz hbot).elim
    · exact htop
  refine ⟨z, ?_⟩
  intro v
  have hv : v ∈ L.eigenspace z := by
    rw [htop]
    exact Submodule.mem_top
  exact Module.End.mem_eigenspace_iff.mp hv

#print axioms pairedTheta_commutant_scalar

end
end FCP.BFSSSU2PhysicalDomainS1A
