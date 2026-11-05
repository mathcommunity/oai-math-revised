import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BUAmbientVectorActionSmoothness
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.BigOperators.Group.List.Defs

/-!
F10BV — smooth finite ordered words in the actual source coordinate-plane curves.

Candidate only until fresh strict compilation and independent PBW/type/axiom
audit. Every factor retains its distinct-label proof and accepted half-angle
normalization. Lists retain the exact multiplication order, including repeated
indices. The word takes values in the actual source Spin group.

Smoothness is asserted for its underlying Clifford-valued map, and for its
actual nine-vector action jointly in the finite parameters and vector.
No subgroup atlas, full parameter derivative, local inverse, tangent-space
identification or group differential is supplied by these ambient statements.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open scoped ContDiff

local instance f10bvLocalNormedAddCommGroup :
    NormedAddCommGroup (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedAddCommGroup
local instance f10bvLocalNormedSpace :
    NormedSpace ℝ (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedSpace

/-- The exact actual plane curve is every-order smooth as an ambient PBW Clifford curve. -/
theorem source9PlaneSpinCurve_coe_contDiff_pbw
    (n : ℕ∞ω) (r s : SpaceIndex) (hrs : r ≠ s) :
    ContDiff ℝ n (fun t : ℝ =>
      ((source9PlaneSpinCurve r s hrs t) : CliffordAlgebra source9Quadratic)) := by
  have hhalf : ContDiff ℝ n (fun t : ℝ => t / 2) :=
    contDiff_id.div_const 2
  have hrotor : ContDiff ℝ n (fun t : ℝ =>
      (Real.cos (t / 2)) • (1 : CliffordAlgebra source9Quadratic) +
        (Real.sin (t / 2)) •
          (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
            CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s))) :=
    (hhalf.cos.smul_const (1 : CliffordAlgebra source9Quadratic)).add
      (hhalf.sin.smul_const
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s)))
  have heq :
      (fun t : ℝ =>
        ((source9PlaneSpinCurve r s hrs t) : CliffordAlgebra source9Quadratic)) =
      (fun t : ℝ =>
        (Real.cos (t / 2)) • (1 : CliffordAlgebra source9Quadratic) +
          (Real.sin (t / 2)) •
            (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
              CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s))) := by
    funext t
    exact source9PlaneSpinCurve_coe r s hrs t
  rw [heq]
  exact hrotor

/-- A finite ordered word of actual source plane curves, with one real parameter per label. -/
noncomputable def source9PlaneSpinWord {k : ℕ}
    (r s : Fin k → SpaceIndex) (hrs : ∀ i, r i ≠ s i) (t : Fin k → ℝ) :
    List (Fin k) → spinGroup source9Quadratic
  | [] => 1
  | i :: l => source9PlaneSpinCurve (r i) (s i) (hrs i) (t i) *
      source9PlaneSpinWord r s hrs t l

/-- The recursion is exactly the ordered list product in the actual group. -/
theorem source9PlaneSpinWord_eq_listProd {k : ℕ}
    (r s : Fin k → SpaceIndex) (hrs : ∀ i, r i ≠ s i)
    (t : Fin k → ℝ) (l : List (Fin k)) :
    source9PlaneSpinWord r s hrs t l =
      (l.map (fun i => source9PlaneSpinCurve (r i) (s i) (hrs i) (t i))).prod := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      simp only [source9PlaneSpinWord, List.map_cons, List.prod_cons, ih]

/-- All parameters zero give the actual source group identity for every ordered word. -/
theorem source9PlaneSpinWord_zero {k : ℕ}
    (r s : Fin k → SpaceIndex) (hrs : ∀ i, r i ≠ s i) (l : List (Fin k)) :
    source9PlaneSpinWord r s hrs 0 l = 1 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      change source9PlaneSpinCurve (r i) (s i) (hrs i) 0 *
        source9PlaneSpinWord r s hrs 0 l = 1
      rw [source9PlaneSpinCurve_zero, one_mul]
      exact ih

/-- Every finite ordered actual source word is jointly smooth in all its real parameters. -/
theorem source9PlaneSpinWord_coe_contDiff_pbw {k : ℕ}
    (n : ℕ∞ω) (r s : Fin k → SpaceIndex) (hrs : ∀ i, r i ≠ s i)
    (l : List (Fin k)) :
    ContDiff ℝ n (fun t : Fin k → ℝ =>
      ((source9PlaneSpinWord r s hrs t l) : CliffordAlgebra source9Quadratic)) := by
  induction l with
  | nil => exact contDiff_const
  | cons i l ih =>
      have hhead : ContDiff ℝ n (fun t : Fin k → ℝ =>
          ((source9PlaneSpinCurve (r i) (s i) (hrs i) (t i)) :
            CliffordAlgebra source9Quadratic)) :=
        (source9PlaneSpinCurve_coe_contDiff_pbw n (r i) (s i) (hrs i)).comp
          (contDiff_apply ℝ ℝ i)
      change ContDiff ℝ n (fun t : Fin k → ℝ =>
        ((source9PlaneSpinCurve (r i) (s i) (hrs i) (t i)) :
          CliffordAlgebra source9Quadratic) *
        ((source9PlaneSpinWord r s hrs t l) : CliffordAlgebra source9Quadratic))
      exact (source9Clifford_mul_contDiff_pbw n).comp₂ hhead ih

/-- The actual word's original nine-vector action is jointly smooth in parameters and vector. -/
theorem source9PlaneSpinWord_vectorAction_contDiff_pbw {k : ℕ}
    (n : ℕ∞ω) (r s : Fin k → SpaceIndex) (hrs : ∀ i, r i ≠ s i)
    (l : List (Fin k)) :
    ContDiff ℝ n (fun tz : (Fin k → ℝ) × (SpaceIndex → ℝ) =>
      source9SpinVectorConjugation (source9PlaneSpinWord r s hrs tz.1 l) tz.2) := by
  have hpair : ContDiff ℝ n
      (fun tz : (Fin k → ℝ) × (SpaceIndex → ℝ) =>
        (((source9PlaneSpinWord r s hrs tz.1 l) : CliffordAlgebra source9Quadratic), tz.2)) :=
    ((source9PlaneSpinWord_coe_contDiff_pbw n r s hrs l).comp contDiff_fst).prodMk
      contDiff_snd
  have h := (source9AmbientVectorConjugation_contDiff_pbw n).comp hpair
  change ContDiff ℝ n (fun tz : (Fin k → ℝ) × (SpaceIndex → ℝ) =>
    source9AmbientVectorConjugation
      ((source9PlaneSpinWord r s hrs tz.1 l) : CliffordAlgebra source9Quadratic) tz.2) at h
  have heq :
      (fun tz : (Fin k → ℝ) × (SpaceIndex → ℝ) =>
        source9AmbientVectorConjugation
          ((source9PlaneSpinWord r s hrs tz.1 l) : CliffordAlgebra source9Quadratic) tz.2) =
      (fun tz : (Fin k → ℝ) × (SpaceIndex → ℝ) =>
        source9SpinVectorConjugation (source9PlaneSpinWord r s hrs tz.1 l) tz.2) := by
    funext tz
    exact source9AmbientVectorConjugation_eq_spin (source9PlaneSpinWord r s hrs tz.1 l) tz.2
  rw [heq] at h
  exact h

#print axioms source9PlaneSpinCurve_coe_contDiff_pbw
#print axioms source9PlaneSpinWord
#print axioms source9PlaneSpinWord_eq_listProd
#print axioms source9PlaneSpinWord_zero
#print axioms source9PlaneSpinWord_coe_contDiff_pbw
#print axioms source9PlaneSpinWord_vectorAction_contDiff_pbw

end
end FCP.BFSSPairedSpin9Clifford
