import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10WOriginalPairedSO48Gamma16KernelReductionProbe

/-!
K1D18V10H-F10X — exact kernel-interface reduction from
original paired G1A SO48 to the source Cl(9) gamma AlgHom.

F10W proved the original SO48 representation has EXACTLY the
same kernel as the genuine source gamma16 orthogonal hom.
F10X removes the remaining orthogonal-subtype wrapper to
identify kernel membership with equality of original source
Clifford-algebra gamma images.

The last declaration states a precise CONDITIONAL faithfulness
criterion: injectivity of the ORIGINAL gamma AlgHom on the
source even Clifford subalgebra implies injectivity of source
Spin9 → original paired SO48. This is NOT a proof of the
hypothesis. No even-Algebra injectivity is assumed globally.

CANDIDATE pending pinned strict fresh warnings-as-errors
Lean compile and four source-exact independent type/axiom
audits; no new axioms, resource-limit changes, surrogate
gamma matrices, topological Spin48 lift, Fock or BFSS claims.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open Matrix

/-- Exact equality of ACTUAL source gamma16 O16 Spin9 images
iff equality of the original source Cl(9) gamma AlgHom values. -/
theorem source9GammaOrthogonal_eq_iff_clifford_gamma
    (g h : spinGroup source9Quadratic) :
    source9SpinGammaOrthogonalHom g =
      source9SpinGammaOrthogonalHom h ↔
    source9GammaCliffordAlgHom
        (g : CliffordAlgebra source9Quadratic) =
      source9GammaCliffordAlgHom
        (h : CliffordAlgebra source9Quadratic) := by
  constructor
  · intro heq
    have hmat := congrArg
      (fun M : Matrix.orthogonalGroup SpinIndex ℝ =>
        (M : GammaMatrix)) heq
    rwa [source9SpinGammaOrthogonalHom_apply,
      source9SpinGammaOrthogonalHom_apply] at hmat
  · intro heq
    apply Subtype.ext
    change source9GammaCliffordAlgHom
      (g : CliffordAlgebra source9Quadratic) =
      source9GammaCliffordAlgHom
        (h : CliffordAlgebra source9Quadratic)
    exact heq

/-- Equality of the EXACT original paired-48 SO48 Spin9 images
iff equality of original source Cl(9) gamma AlgHom values. -/
theorem source9OriginalPairedSO48_eq_iff_clifford_gamma
    (g h : spinGroup source9Quadratic) :
    source9SpinOriginalPaired48SpecialOrthogonalHom g =
      source9SpinOriginalPaired48SpecialOrthogonalHom h ↔
    source9GammaCliffordAlgHom
        (g : CliffordAlgebra source9Quadratic) =
      source9GammaCliffordAlgHom
        (h : CliffordAlgebra source9Quadratic) := by
  exact (source9OriginalPairedSO48_eq_iff_gamma16 g h).trans
    (source9GammaOrthogonal_eq_iff_clifford_gamma g h)

/-- The original paired Spin9 SO48 kernel is PRECISELY the
preimage of 1 under the actual source Cl(9) gamma AlgHom. -/
theorem source9OriginalPairedSO48_mem_ker_iff_clifford_one
    (g : spinGroup source9Quadratic) :
    g ∈ source9SpinOriginalPaired48SpecialOrthogonalHom.ker ↔
    source9GammaCliffordAlgHom
        (g : CliffordAlgebra source9Quadratic) = 1 := by
  have heq := source9OriginalPairedSO48_eq_iff_clifford_gamma
    g (1 : spinGroup source9Quadratic)
  have hOne :
      source9GammaCliffordAlgHom
          ((1 : spinGroup source9Quadratic) :
            CliffordAlgebra source9Quadratic) =
        (1 : GammaMatrix) := by
    calc
      source9GammaCliffordAlgHom
          ((1 : spinGroup source9Quadratic) :
            CliffordAlgebra source9Quadratic) =
          ((source9SpinGammaOrthogonalHom
              (1 : spinGroup source9Quadratic)) : GammaMatrix) :=
        (source9SpinGammaOrthogonalHom_apply
          (1 : spinGroup source9Quadratic)).symm
      _ = 1 := by
        rw [map_one]
        rfl
  simpa only [MonoidHom.mem_ker, map_one, hOne] using heq

/-- The MISSING substantive obligation is explicitly stated:
if the ACTUAL original source Cl(9) gamma AlgHom is injective
ON THE EVEN Clifford subalgebra, then the genuine source
Spin9→original paired SO48 representation is injective.
THIS HYPOTHESIS IS NOT CONSTRUCTED OR PROVED HERE. -/
theorem source9OriginalPairedSO48_injective_of_even_gamma_injective
    (hEven :
      ∀ a b : CliffordAlgebra source9Quadratic,
        a ∈ CliffordAlgebra.even source9Quadratic →
        b ∈ CliffordAlgebra.even source9Quadratic →
        source9GammaCliffordAlgHom a =
          source9GammaCliffordAlgHom b → a = b) :
    Function.Injective
      source9SpinOriginalPaired48SpecialOrthogonalHom := by
  intro g h heq
  have hGamma :
      source9GammaCliffordAlgHom
          (g : CliffordAlgebra source9Quadratic) =
        source9GammaCliffordAlgHom
          (h : CliffordAlgebra source9Quadratic) :=
    (source9OriginalPairedSO48_eq_iff_clifford_gamma g h).mp heq
  have hgEven : (g : CliffordAlgebra source9Quadratic) ∈
      CliffordAlgebra.even source9Quadratic :=
    ((spinGroup.mem_iff).mp g.property).2
  have hhEven : (h : CliffordAlgebra source9Quadratic) ∈
      CliffordAlgebra.even source9Quadratic :=
    ((spinGroup.mem_iff).mp h.property).2
  apply Subtype.ext
  exact hEven _ _ hgEven hhEven hGamma

#print axioms source9GammaOrthogonal_eq_iff_clifford_gamma
#print axioms source9OriginalPairedSO48_eq_iff_clifford_gamma
#print axioms source9OriginalPairedSO48_mem_ker_iff_clifford_one
#print axioms source9OriginalPairedSO48_injective_of_even_gamma_injective

end
end FCP.BFSSPairedSpin9Clifford
