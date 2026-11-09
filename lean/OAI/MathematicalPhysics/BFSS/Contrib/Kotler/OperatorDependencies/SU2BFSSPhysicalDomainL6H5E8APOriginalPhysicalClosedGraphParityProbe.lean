import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AOOriginalPhysicalCoreGraphGeneratorParityProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AJOriginalFullL2ParityUnitaryProbe
import Mathlib.Topology.Homeomorph.Defs

/-!
# H5E8AP — original restricted sixteen-charge CLOSED GRAPH under parity

Source-qualified AO supplies both directions of the *actual* gauge-invariant
sixteen-charge graph generator correspondence. Original AI/AJ prove genuine
spatial parity on the real FullL2 Hilbert space. This probe establishes a
homeomorphism of the exact FullL2 × (SpinIndex → FullL2) graph ambient space
and transports the closure of the ORIGINAL source physical core graph.

This is source operator graph geometry, not manuscript/Lean representation
identity, not equality of arbitrary full-space and physical restrictions,
and not yet a theorem identifying the associated Hamiltonian domains.

Pin the original BFSS source, Lean and Mathlib. Require fresh .olean,
all root axiom audits and no sorryAx; no inference from a skipped CI gate.
-/

set_option autoImplicit false
set_option maxHeartbeats 240000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AP
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AD
open FCP.BFSSSU2PhysicalDomainL6H5E8AI
open FCP.BFSSSU2PhysicalDomainL6H5E8AJ
open FCP.BFSSSU2PhysicalDomainL6H5E8AN
open FCP.BFSSSU2PhysicalDomainL6H5E8AO

/-- Applying the source pair parity twice is literally the identity,
including every one of the sixteen source spinor output components. -/
theorem originalPhysicalGraphPairParity_twice {N : ℕ}
    (p : FullL2 N × (SpinIndex → FullL2 N)) :
    originalPhysicalGraphPairParity
      (originalPhysicalGraphPairParity p) = p := by
  change
    (originalFullL2Parity (originalFullL2Parity p.1),
      fun α => originalFullL2Parity (originalFullL2Parity (p.2 α))) = p
  cases p with
  | mk x y =>
    apply Prod.ext
    · exact originalFullL2Parity_involutive x
    · funext α
      exact originalFullL2Parity_involutive (y α)

/-- Continuity on the exact original product Hilbert topology:
first source FullL2 output and the full finite spinor function output. -/
theorem originalPhysicalGraphPairParity_continuous {N : ℕ} :
    Continuous (originalPhysicalGraphPairParity (N := N)) := by
  change Continuous (fun p : FullL2 N × (SpinIndex → FullL2 N) =>
    (originalFullL2Parity p.1,
      fun α => originalFullL2Parity (p.2 α)))
  have hf : Continuous (fun p : FullL2 N × (SpinIndex → FullL2 N) =>
      originalFullL2Parity p.1) :=
    (originalFullL2Parity (N := N)).continuous.comp continuous_fst
  have hg : Continuous (fun p : FullL2 N × (SpinIndex → FullL2 N) =>
      fun α => originalFullL2Parity (p.2 α)) := by
    apply continuous_pi
    intro α
    exact (originalFullL2Parity (N := N)).continuous.comp
      ((continuous_apply α).comp continuous_snd)
  exact hf.prodMk hg

/-- A genuine homeomorphism, using the actual source parity as its
own inverse. We do not yet promote it to a Hilbert product unitary. -/
noncomputable def originalPhysicalGraphPairHomeomorph {N : ℕ} :
    (FullL2 N × (SpinIndex → FullL2 N)) ≃ₜ
      (FullL2 N × (SpinIndex → FullL2 N)) where
  toEquiv :=
    { toFun := originalPhysicalGraphPairParity
      invFun := originalPhysicalGraphPairParity
      left_inv := originalPhysicalGraphPairParity_twice
      right_inv := originalPhysicalGraphPairParity_twice }
  continuous_toFun := originalPhysicalGraphPairParity_continuous
  continuous_invFun := originalPhysicalGraphPairParity_continuous

/-- The literal source original gauge-invariant sixteen-charge
core graph as a SET, not an invented closed or maximal operator. -/
def originalPhysicalCoreGraphSet {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    Set (FullL2 N × (SpinIndex → FullL2 N)) :=
  Set.range (fun f : G.invariantCore =>
    (coreToL2 f.val, M.chargeVector f.val))

/-- Reusable, source-independent SET transport: a map carries the range
of f exactly to the range of g when both inclusions have witnesses.
Prove before specialization so no concrete Fock/source graph is reduced
while solving Set.image/Set.range membership. -/
private theorem image_range_of_two_way {A B X : Type*}
    (p : X → X) (f : A → X) (g : B → X)
    (forward : ∀ a : A, ∃ b : B, g b = p (f a))
    (backward : ∀ b : B, ∃ a : A, p (f a) = g b) :
    p '' Set.range f = Set.range g := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    obtain ⟨b, hb⟩ := forward a
    exact ⟨b, hb⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, ha⟩ := backward b
    exact ⟨f a, ⟨a, rfl⟩, ha⟩

/-- AO's two qualified source directions imply exact equality of the
actual restricted core graph generator SETS after source parity.
Specialize an already proven abstract set lemma; no huge source reduction. -/
theorem originalPhysicalCoreGraphSet_image {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    originalPhysicalGraphPairParity '' originalPhysicalCoreGraphSet M G =
      originalPhysicalCoreGraphSet (oppositeGamma M)
        (originalOppositeGammaGaugeData M G) := by
  change originalPhysicalGraphPairParity ''
      Set.range (fun f : G.invariantCore =>
        (coreToL2 f.val, M.chargeVector f.val)) =
    Set.range (fun f' : (originalOppositeGammaGaugeData M G).invariantCore =>
      (coreToL2 f'.val, (oppositeGamma M).chargeVector f'.val))
  exact image_range_of_two_way
    (originalPhysicalGraphPairParity (N := N))
    (fun f : G.invariantCore =>
      (coreToL2 f.val, M.chargeVector f.val))
    (fun f' : (originalOppositeGammaGaugeData M G).invariantCore =>
      (coreToL2 f'.val, (oppositeGamma M).chargeVector f'.val))
    (originalPhysicalCorePair_to_opposite M G)
    (originalPhysicalCorePair_from_opposite M G)

/-- Genuine CLOSED original physical sixteen-charge graph transport.
Closure is taken in the exact paired FullL2 × sixteen-FullL2 product.
Nothing about the independently specified paper Hamiltonian is assumed. -/
theorem originalPhysicalClosedGraphSet_image {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    originalPhysicalGraphPairParity ''
        closure (originalPhysicalCoreGraphSet M G) =
      closure (originalPhysicalCoreGraphSet (oppositeGamma M)
        (originalOppositeGammaGaugeData M G)) := by
  change (originalPhysicalGraphPairHomeomorph (N := N)) ''
      closure (originalPhysicalCoreGraphSet M G) =
    closure (originalPhysicalCoreGraphSet (oppositeGamma M)
      (originalOppositeGammaGaugeData M G))
  rw [(originalPhysicalGraphPairHomeomorph (N := N)).image_closure]
  exact congrArg closure (originalPhysicalCoreGraphSet_image M G)

#print axioms originalPhysicalGraphPairParity_twice
#print axioms originalPhysicalGraphPairParity_continuous
#print axioms originalPhysicalGraphPairHomeomorph
#print axioms originalPhysicalCoreGraphSet
#print axioms originalPhysicalCoreGraphSet_image
#print axioms originalPhysicalClosedGraphSet_image

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AP
