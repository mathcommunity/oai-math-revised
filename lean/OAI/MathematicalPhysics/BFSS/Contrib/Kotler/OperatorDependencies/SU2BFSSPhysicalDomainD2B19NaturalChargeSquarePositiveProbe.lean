import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B18NaturalChargeAdjointSquareProbe
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# BFSS SU2 D2B19 — positivity and symmetry of the physical natural adjoint-square

PROSPECTIVE until exact pinned compiler and axioms pass.

The natural product from D2B18 is tested against the actual formal adjoint
identity qualified in D2B17. For all ψ in dom(T†T), the Hilbert pairing
⟪T†T ψ, ψ⟫ is exactly ⟪T ψ, T ψ⟫, giving a nonnegative real energy.
The product is formally symmetric on its natural domain. This is NOT
yet the self-adjointness theorem or a manuscript Hamiltonian identity.

Proof architecture informed by Keisuke Suzuki, QuantumSystem
Analysis/UnboundedOperator/VonNeumann.lean, Git
a2bb99fcb82c820f040004a2f99c875575c72efd (Apache-2.0).
No external code is imported, and no new axioms are admitted.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B19
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2B17
open FCP.BFSSSU2PhysicalDomainD2B18
open RCLike
open scoped ComplexConjugate

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Natural-domain adjoint-square Hilbert pairing, using only the
actual formal-adjoint identity and no analytic assumptions on products. -/
theorem naturalFormalProduct_inner
    (T : E →ₗ.[ℂ] F) (A : F →ₗ.[ℂ] E)
    (hA : A.IsFormalAdjoint T)
    (u : (naturalComp A T).domain) :
    inner ℂ (naturalComp A T u) (u : E) =
      inner ℂ (T ⟨u, naturalComp_domain_le u.property⟩)
        (T ⟨u, naturalComp_domain_le u.property⟩) := by
  rw [naturalComp_apply]
  exact hA ⟨_, naturalComp_apply_mem u⟩
    ⟨u, naturalComp_domain_le u.property⟩

/-- The natural product is formally symmetric as a consequence of
the true Hilbert adjoint pairing; this alone is not self-adjointness. -/
theorem naturalFormalProduct_symmetric
    (T : E →ₗ.[ℂ] F) (A : F →ₗ.[ℂ] E)
    (hA : A.IsFormalAdjoint T) :
    (naturalComp A T).IsFormalAdjoint (naturalComp A T) := by
  intro x y
  have h₁ := hA
    (⟨T ⟨x, naturalComp_domain_le x.property⟩, naturalComp_apply_mem x⟩)
    (⟨y, naturalComp_domain_le y.property⟩)
  have h₂ := hA
    (⟨T ⟨y, naturalComp_domain_le y.property⟩, naturalComp_apply_mem y⟩)
    (⟨x, naturalComp_domain_le x.property⟩)
  rw [naturalComp_apply, naturalComp_apply]
  calc
    _ = _ := h₁
    _ = conj _ := (inner_conj_symm _ _).symm
    _ = conj _ := congrArg conj h₂.symm
    _ = _ := inner_conj_symm _ _

variable (M : AlgebraData 2) (G : M.GaugeData)

theorem sourcePhysicalChargeAdjointSquare_inner
    (u : (sourcePhysicalChargeAdjointSquare M G).domain) :
    inner ℂ (sourcePhysicalChargeAdjointSquare M G u)
      (u : G.physicalSpace) =
      inner ℂ
        (sourcePhysicalHilbertChargeColumn M G
          ⟨u, naturalComp_domain_le u.property⟩)
        (sourcePhysicalHilbertChargeColumn M G
          ⟨u, naturalComp_domain_le u.property⟩) :=
  naturalFormalProduct_inner _ _
    (sourceOriginalPhysicalChargeAdjoint_isFormalAdjoint M G) u

theorem sourcePhysicalChargeAdjointSquare_symmetric :
    (sourcePhysicalChargeAdjointSquare M G).IsFormalAdjoint
      (sourcePhysicalChargeAdjointSquare M G) :=
  naturalFormalProduct_symmetric _ _
    (sourceOriginalPhysicalChargeAdjoint_isFormalAdjoint M G)

/-- The source physical adjoint-square energy is the *exact* squared
sixteen-charge Hilbert norm on its actual natural domain. -/
theorem sourcePhysicalChargeAdjointSquare_energy
    (u : (sourcePhysicalChargeAdjointSquare M G).domain) :
    re (inner ℂ (sourcePhysicalChargeAdjointSquare M G u)
      (u : G.physicalSpace)) =
      ‖sourcePhysicalHilbertChargeColumn M G
        ⟨u, naturalComp_domain_le u.property⟩‖ ^ 2 := by
  rw [sourcePhysicalChargeAdjointSquare_inner M G u, inner_self_eq_norm_sq]

theorem sourcePhysicalChargeAdjointSquare_nonneg
    (u : (sourcePhysicalChargeAdjointSquare M G).domain) :
    0 ≤ re (inner ℂ (sourcePhysicalChargeAdjointSquare M G u)
      (u : G.physicalSpace)) := by
  rw [sourcePhysicalChargeAdjointSquare_energy M G u]
  exact sq_nonneg _

#print axioms naturalFormalProduct_inner
#print axioms naturalFormalProduct_symmetric
#print axioms sourcePhysicalChargeAdjointSquare_inner
#print axioms sourcePhysicalChargeAdjointSquare_symmetric
#print axioms sourcePhysicalChargeAdjointSquare_energy
#print axioms sourcePhysicalChargeAdjointSquare_nonneg

end
end FCP.BFSSSU2PhysicalDomainD2B19
