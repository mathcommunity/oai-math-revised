import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V29AllSpin48CliffordGeneratorConjugationProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-! Owner import from FCP cc608e2282e1b32bb11bbb64424e4775b28138e2,
original source blob 59d40c5c74cc4803a6a6096cfe5ea87c800bd7f9.
Only imports and this provenance comment are adapted. Definitions, theorem
statements and proof bodies below are source-exact. Local candidate only
until an independent owner strict gate passes. -/

/-!
S1V30 — original SOURCE-SIZED Clifford generator injectivity via the
pinned Mathlib Clifford-to-exterior linear equivalence.

This is the ACTUAL S1V0.source48Quadratic on Fin 24 × Fin 2, not a
surrogate form or a separately assumed module embedding. The pinned
Mathlib Clifford changeForm equivalence carries generator ι(Q)v to
degree-one exterior generator ι(0)v; the exterior degree-one embedding
has an actual left inverse, hence is injective.

Two UNCOMPILED candidate roots, isolated behind their own strict gate.
No unproved Clifford faithfulness, no extra axiom, no claimed Spin→SO
projection, continuous covering, global SU2 lift, Fock intertwiner,
source physical supercharge identification or BFSS spectral gap.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000

namespace FCP.BFSSS1V30
noncomputable section

open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- The exact source real Clifford generator maps to the exact
degree-one exterior generator through pinned Mathlib's char-0
Clifford-to-exterior linear equivalence. -/
theorem source48_cliffordGenerator_equivExterior
    (v : Source48Vector) :
    (CliffordAlgebra.equivExterior Q)
        (CliffordAlgebra.ι Q v) =
      ExteriorAlgebra.ι ℝ v := by
  change
    CliffordAlgebra.changeForm
        (CliffordAlgebra.changeForm.associated_neg_proof (Q := Q))
        (CliffordAlgebra.ι Q v) =
      CliffordAlgebra.ι (0 : QuadraticForm ℝ Source48Vector) v
  exact CliffordAlgebra.changeForm_ι
    (h := CliffordAlgebra.changeForm.associated_neg_proof (Q := Q)) v

/-- The genuine original 48-real canonical Clifford generator map
is injective. No positivity or basis reduction is assumed: the
degree-one exterior embedding provides a proved left inverse after
transport through the pinned Clifford-to-exterior equivalence. -/
theorem source48_cliffordGenerator_injective :
    Function.Injective (CliffordAlgebra.ι Q) := by
  intro v w h
  apply (ExteriorAlgebra.ι_inj ℝ v w).mp
  calc
    ExteriorAlgebra.ι ℝ v =
      (CliffordAlgebra.equivExterior Q)
        (CliffordAlgebra.ι Q v) :=
          (source48_cliffordGenerator_equivExterior v).symm
    _ = (CliffordAlgebra.equivExterior Q)
          (CliffordAlgebra.ι Q w) :=
            congrArg (CliffordAlgebra.equivExterior Q) h
    _ = ExteriorAlgebra.ι ℝ w :=
          source48_cliffordGenerator_equivExterior w

#print axioms source48_cliffordGenerator_equivExterior
#print axioms source48_cliffordGenerator_injective

end
end FCP.BFSSS1V30
