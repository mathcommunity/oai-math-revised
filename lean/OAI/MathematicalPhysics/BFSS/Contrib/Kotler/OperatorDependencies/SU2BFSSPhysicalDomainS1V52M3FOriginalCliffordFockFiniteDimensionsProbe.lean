import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52M3EOriginalComplexCliffordPBWBasisProbe
import Mathlib.Data.Fintype.Powerset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
S1V52M3F — symbolic dimensions of the ACTUAL original Clifford and
24-complex-mode Fock spaces. M3E supplied a strict-accepted PBW basis;
M3D supplied strict-accepted full-image surjectivity.

This proof candidate separately checks both underlying dimensions
without building all 2^48 PBW monomials or Fock operators. The
continuous-linear endomorphism dimension and source Clifford
faithfulness are NOT yet claimed or proved.

Research only until exact source/axiom-gated Lean compilation passes.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52M3F
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V52M3E

/-- Cardinality of the actual original Spin(48) real-Majorana
coordinate labels, not a substituted 48-element type. -/
theorem originalSource48Label_card :
    Fintype.card Source48Label = 48 := by
  norm_num [Source48Label, Fintype.card_prod]

/-- Complex rank of the exact original Clifford algebra.  This is
symbolic cardinal arithmetic on the accepted PBW basis index type. -/
theorem originalComplexClifford_finrank_pow :
    Module.finrank ℂ
        (CliffordAlgebra (source48Quadratic.baseChange ℂ)) =
      2 ^ 48 := by
  rw [originalComplexClifford_finrank, Fintype.card_finset,
    originalSource48Label_card]

/-- The actual source original SU(2) Fock space has 24 complex
creation modes and therefore complex dimension 2^24. -/
theorem originalFock_finrank :
    Module.finrank ℂ (Fermion 2) = 2 ^ 24 := by
  change Module.finrank ℂ
    (EuclideanSpace ℂ (Fin (2 ^ (8 * colorDim 2)))) = 2 ^ 24
  rw [finrank_euclideanSpace_fin]
  norm_num [colorDim]

#print axioms originalSource48Label_card
#print axioms originalComplexClifford_finrank_pow
#print axioms originalFock_finrank

end
end FCP.BFSSS1V52M3F
