import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8JOriginalColorIntegratedUnitaryLipschitzProbe
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
L6H5E8K — closure of the graph of the ACTUAL original SU2
BFSS color infinitesimal generator on its EXACT maximal strong
differentiability domain in the genuine FullL2 Hilbert space.

H5E8H + H5E8I characterize (v,w) in the original graph
by the identity
  ∀ t : ℝ, ∫_0^t U_c(s) w ds = U_c(t) v - v.
H5E8J gives the original norm bound
  ‖integral_t(w) - integral_t(z)‖ ≤ |t| ‖w-z‖.
Each fixed-time equation is a CLOSED equalizer of two
continuous functions of (v,w); arbitrary intersections
of closed sets are closed.

The small generic topological argument is proven separately
from the source-specific CLM, inverse boson pullback and
48-Majorana Fock action. No surrogate dynamics and no change
to the ORIGINAL +i gauge conventions. Graph closedness is NOT
by itself a theorem of essential skew-adjointness, generator
spectra or the BFSS Hamiltonian.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8K
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6G7W
open FCP.BFSSSU2PhysicalDomainL6H5A
open FCP.BFSSSU2PhysicalDomainL6H5E8E
open FCP.BFSSSU2PhysicalDomainL6H5E8H
open FCP.BFSSSU2PhysicalDomainL6H5E8I
open FCP.BFSSSU2PhysicalDomainL6H5E8J
open MeasureTheory

/-- Abstract topological principle. A graph characterized by
Banach-valued integral equalities at every time is closed as
soon as its fixed-time integral operators are continuous.
No BFSS-specific unfolding occurs in this proof. -/
theorem abstract_integral_characterized_graph_isClosed
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (U : ℝ → E →L[ℝ] E)
    (hcontIntegral : ∀ t : ℝ,
      Continuous (fun w : E => ∫ s in (0 : ℝ)..t, U s w))
    (S : Set (E × E))
    (hchar : ∀ (v w : E),
      (v, w) ∈ S ↔
        ∀ t : ℝ, (∫ s in (0 : ℝ)..t, U s w) = U t v - v) :
    IsClosed S := by
  have hset :
      S = ⋂ t : ℝ,
        {p : E × E |
          (∫ s in (0 : ℝ)..t, U s p.2) = U t p.1 - p.1} := by
    ext p
    constructor
    · intro hp
      apply Set.mem_iInter.mpr
      intro t
      exact (hchar p.1 p.2).mp hp t
    · intro hp
      apply (hchar p.1 p.2).mpr
      intro t
      exact Set.mem_iInter.mp hp t
  rw [hset]
  apply isClosed_iInter
  intro t
  have hl :
      Continuous (fun p : E × E =>
        ∫ s in (0 : ℝ)..t, U s p.2) :=
    (hcontIntegral t).comp continuous_snd
  have hr :
      Continuous (fun p : E × E => U t p.1 - p.1) :=
    ((U t).continuous.comp continuous_fst).sub continuous_fst
  exact isClosed_eq hl hr

/-- Exactly the graph of the ORIGINAL color generator as a
set in the actual FullL2 x FullL2 product Hilbert space.
The existential packages domain membership, not a new axiom
or extension. -/
def actualOriginalColorGeneratorGraph
    (c : ColorIndex 2) : Set (FullL2 2 × FullL2 2) :=
  {p | ∃ hv : p.1 ∈ actualOriginalColorGeneratorDomainSubmodule c,
    actualOriginalColorGeneratorLinear c ⟨p.1, hv⟩ = p.2}

/-- H5E8H/H5E8I give an if-and-only-if description of
the exact original maximal color Gauss operator graph. -/
theorem actualOriginalColorGeneratorGraph_iff_integral
    (c : ColorIndex 2) (v w : FullL2 2) :
    (v, w) ∈ actualOriginalColorGeneratorGraph c ↔
      ∀ t : ℝ,
        (∫ s in (0 : ℝ)..t,
          actualOriginalFullL2GaugePairCLM
            (sourcePlusIGaugeCurve c s) w) =
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c t) v - v := by
  constructor
  · rintro ⟨hv, hgen⟩
    intro t
    have he := actualOriginalColorGenerator_orbit_integral_eq_sub c
      (⟨v, hv⟩ : actualOriginalColorGeneratorDomainSubmodule c) t
    rw [hgen] at he
    exact he
  · intro hidentity
    exact ⟨actualOriginalColorIntegral_implies_generatorDomain
      c v w hidentity,
      actualOriginalColorIntegral_implies_generator_eq c v w hidentity⟩

/-- A fixed original color-time integrated gauge orbit is a
continuous FullL2 to FullL2 map; this is precisely the
strong result H5E8J adds to prior source orbit continuity. -/
theorem actualOriginalColorOrbit_integral_continuous
    (c : ColorIndex 2) (t : ℝ) :
    Continuous (fun w : FullL2 2 =>
      ∫ s in (0 : ℝ)..t,
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c s) w) := by
  have hLip :
      LipschitzWith (Real.toNNReal |t|)
        (fun w : FullL2 2 =>
          ∫ s in (0 : ℝ)..t,
            actualOriginalFullL2GaugePairCLM
              (sourcePlusIGaugeCurve c s) w) := by
    apply LipschitzWith.of_dist_le' (K := |t|)
    intro w z
    have h := actualOriginalColorOrbit_integral_lipschitz c w z t
    simpa only [dist_eq_norm, mul_comm] using h
  exact hLip.continuous

/-- MAIN TARGET: The maximal original BFSS color Gauss
infinitesimal generator has CLOSED GRAPH as an unbounded
operator between the exact full source Hilbert spaces.
The graph is NOT a new model: see its definition/iff above. -/
theorem actualOriginalColorGeneratorGraph_isClosed
    (c : ColorIndex 2) :
    IsClosed (actualOriginalColorGeneratorGraph c) := by
  let U : ℝ → FullL2 2 →L[ℝ] FullL2 2 :=
    fun s => (actualOriginalFullL2GaugePairCLM
      (sourcePlusIGaugeCurve c s)).restrictScalars ℝ
  have hc : ∀ t : ℝ,
      Continuous (fun w : FullL2 2 =>
        ∫ s in (0 : ℝ)..t, U s w) := by
    intro t
    exact actualOriginalColorOrbit_integral_continuous c t
  have hchar : ∀ (v w : FullL2 2),
      (v,w) ∈ actualOriginalColorGeneratorGraph c ↔
        ∀ t : ℝ,
          (∫ s in (0 : ℝ)..t, U s w) = U t v - v := by
    intro v w
    exact actualOriginalColorGeneratorGraph_iff_integral c v w
  exact abstract_integral_characterized_graph_isClosed U hc
    (actualOriginalColorGeneratorGraph c) hchar

#print axioms abstract_integral_characterized_graph_isClosed
#print axioms actualOriginalColorGeneratorGraph
#print axioms actualOriginalColorGeneratorGraph_iff_integral
#print axioms actualOriginalColorOrbit_integral_continuous
#print axioms actualOriginalColorGeneratorGraph_isClosed
#check @actualOriginalColorGeneratorGraph_isClosed

end
end FCP.BFSSSU2PhysicalDomainL6H5E8K
