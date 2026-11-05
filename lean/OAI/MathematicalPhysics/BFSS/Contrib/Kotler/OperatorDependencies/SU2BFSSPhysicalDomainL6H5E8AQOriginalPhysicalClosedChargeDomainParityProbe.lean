import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8APOriginalPhysicalClosedGraphParityProbe

/-!
# H5E8AQ — original closed physical sixteen-charge DOMAIN under parity

H5E8AP is a source-pinned, axiom-clean homeomorphism between the
closures of the exact original gauge-restricted 16-charge core graphs
for M and oppositeGamma M (with its explicitly reconstructed GaugeData).

This module isolates an abstract involutive image/membership law FIRST,
then instantiates the literal source graph. It proves the exact SET of
first-coordinate graph inputs is transported by original FullL2 parity.
No assumption that a full-space closure equals a physical restricted
closure; no new source operator or Hamiltonian is introduced.

Downstream source normalization: accepted H5E8AB proves that
G.deformedModelGraph 1 0 is exactly this core-graph closure. This
module does not import G4K9D/H5E8AB and does NOT yet independently
certify an explicit D2B12 LinearPMap or any associated Hamiltonian
operator domain. That joint-dependency bridge remains a separate gate.
-/

set_option autoImplicit false
set_option maxHeartbeats 240000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AQ
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AD
open FCP.BFSSSU2PhysicalDomainL6H5E8AI
open FCP.BFSSSU2PhysicalDomainL6H5E8AJ
open FCP.BFSSSU2PhysicalDomainL6H5E8AN
open FCP.BFSSSU2PhysicalDomainL6H5E8AO
open FCP.BFSSSU2PhysicalDomainL6H5E8AP

/-- Generic elementary set transport, proved WITHOUT original Fock
operators or dependent BFSS graph expansions. -/
private theorem mem_iff_of_involutive_image {X : Type*}
    (p : X → X) (hp : ∀ x, p (p x) = x)
    (S T : Set X) (heq : p '' S = T) (x : X) :
    x ∈ S ↔ p x ∈ T := by
  constructor
  · intro hx
    rw [← heq]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have he : x = y := by
      calc
        x = p (p x) := (hp x).symm
        _ = p (p y) := congrArg p hxy.symm
        _ = y := hp y
    exact he ▸ hy

/-- Exact original CLOSED restricted physical graph membership:
both the input and every one of the sixteen charge outputs transform,
and the source GaugeData is explicitly transported across gamma index. -/
theorem originalPhysicalClosedGraph_mem_iff {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (x : FullL2 N) (y : SpinIndex → FullL2 N) :
    (x,y) ∈ closure (originalPhysicalCoreGraphSet M G) ↔
      (originalFullL2Parity x,
        fun α => originalFullL2Parity (y α)) ∈
      closure (originalPhysicalCoreGraphSet (oppositeGamma M)
        (originalOppositeGammaGaugeData M G)) := by
  exact mem_iff_of_involutive_image
    (originalPhysicalGraphPairParity (N := N))
    (originalPhysicalGraphPairParity_twice (N := N))
    (closure (originalPhysicalCoreGraphSet M G))
    (closure (originalPhysicalCoreGraphSet (oppositeGamma M)
      (originalOppositeGammaGaugeData M G)))
    (originalPhysicalClosedGraphSet_image M G)
    (x,y)

/-- Literal domain as the SET of first coordinates of the original
gauge-restricted minimal closed sixteen-charge graph.
It is NOT an arbitrarily defined maximal differential domain. -/
def originalPhysicalClosedChargeDomainSet {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) : Set (FullL2 N) :=
  {x | ∃ y : SpinIndex → FullL2 N,
    (x,y) ∈ closure (originalPhysicalCoreGraphSet M G)}

/-- Domain membership in the true SOURCE original closed graph is
transported both directions by original L2 parity. -/
theorem originalPhysicalClosedChargeDomain_mem_iff {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) (x : FullL2 N) :
    x ∈ originalPhysicalClosedChargeDomainSet M G ↔
      originalFullL2Parity x ∈
        originalPhysicalClosedChargeDomainSet (oppositeGamma M)
          (originalOppositeGammaGaugeData M G) := by
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨fun α => originalFullL2Parity (y α),
      (originalPhysicalClosedGraph_mem_iff M G x y).mp hy⟩
  · rintro ⟨y,hy⟩
    let z : SpinIndex → FullL2 N :=
      fun α => originalFullL2Parity (y α)
    refine ⟨z, (originalPhysicalClosedGraph_mem_iff M G x z).mpr ?_⟩
    have hz : (fun α => originalFullL2Parity (z α)) = y := by
      funext α
      exact originalFullL2Parity_involutive (y α)
    simpa only [hz] using hy

/-- Exact image equality of the actual minimal-closed-graph first
coordinate domain. No extra operator-domain assumption is inserted. -/
theorem originalPhysicalClosedChargeDomain_image {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    originalFullL2Parity '' originalPhysicalClosedChargeDomainSet M G =
      originalPhysicalClosedChargeDomainSet (oppositeGamma M)
        (originalOppositeGammaGaugeData M G) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (originalPhysicalClosedChargeDomain_mem_iff M G y).mp hy
  · intro hx
    refine ⟨originalFullL2Parity x, ?_, originalFullL2Parity_involutive x⟩
    exact (originalPhysicalClosedChargeDomain_mem_iff M G
      (originalFullL2Parity x)).mpr
      (by simpa only [originalFullL2Parity_involutive] using hx)

#print axioms originalPhysicalClosedGraph_mem_iff
#print axioms originalPhysicalClosedChargeDomainSet
#print axioms originalPhysicalClosedChargeDomain_mem_iff
#print axioms originalPhysicalClosedChargeDomain_image

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AQ
