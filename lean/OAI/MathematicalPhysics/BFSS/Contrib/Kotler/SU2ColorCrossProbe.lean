import Mathlib
import OAI.MathematicalPhysics.BFSS.PotentialBasis
import OAI.Analysis.CharacterCriterion.Pauli

/-!
# Concrete SU(2) color algebra, first independently compiled gate

This deliberately proves only a finite-dimensional scalar identity, not
existence of OAI.BFSSQuantum.AlgebraData 2, gauge covariance, or the
positive-eigenvalue theorem. The normalization sqrt 2 is that in the
October 5, 2026 relative SU(2) BFSS manuscript.

Next unproved bridge obligations: exhibit the normalized Pauli basis
T_a = sigma_a / sqrt 2, show f_abc = sqrt 2 * epsilon_abc,
and prove that OAI's deformedBosonicPotential 1 0 specializes to
the concrete wedge potential.
-/

namespace FCP.BFSSSU2
noncomputable section
open Finset

/-- The oriented Levi-Civita symbol in three color dimensions. -/
def epsilon3 : Fin 3 → Fin 3 → Fin 3 → ℝ
  | 0, 1, 2 => 1
  | 1, 2, 0 => 1
  | 2, 0, 1 => 1
  | 0, 2, 1 => -1
  | 2, 1, 0 => -1
  | 1, 0, 2 => -1
  | _, _, _ => 0

/-- The components of the ordinary oriented cross product. -/
def colorCross (u v : Fin 3 → ℝ) : Fin 3 → ℝ
  | 0 => u 1 * v 2 - u 2 * v 1
  | 1 => u 2 * v 0 - u 0 * v 2
  | 2 => u 0 * v 1 - u 1 * v 0

/-- A normalized structure-constant contraction becomes sqrt(2) times the cross product. -/
lemma epsilon3_contraction (u v : Fin 3 → ℝ) (a : Fin 3) :
    (∑ b : Fin 3, ∑ c : Fin 3,
        (Real.sqrt 2 * epsilon3 a b c) * u b * v c) =
      Real.sqrt 2 * colorCross u v a := by
  fin_cases a <;> simp [epsilon3, colorCross, Fin.sum_univ_three] <;> ring

/-- Half the squared length of the normalized bracket equals its three squared minors. -/
lemma normalized_cross_energy (u v : Fin 3 → ℝ) :
    (1/2 : ℝ) * ∑ a : Fin 3,
      (∑ b : Fin 3, ∑ c : Fin 3,
        (Real.sqrt 2 * epsilon3 a b c) * u b * v c)^2 =
      (u 0 * v 1 - u 1 * v 0)^2 +
      (u 0 * v 2 - u 2 * v 0)^2 +
      (u 1 * v 2 - u 2 * v 1)^2 := by
  simp_rw [epsilon3_contraction]
  rw [Fin.sum_univ_three]
  simp only [colorCross, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring


/-- The standard ordered Pauli matrices (σₓ, σᵧ, σ_z) over ℂ. -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, 1; 1, 0]
  | 1 => !![0, -Complex.I; Complex.I, 0]
  | 2 => !![1, 0; 0, -1]

/--
Unnormalized Pauli commutators. This is a finite, fully explicit matrix
check. The normalized Tₐ=σₐ/√2 identity is a *subsequent* milestone.
-/
lemma pauli_commutator (a b : Fin 3) :
    pauli a * pauli b - pauli b * pauli a =
      (2 * Complex.I) • (∑ c : Fin 3, (epsilon3 a b c : ℂ) • pauli c) := by
  fin_cases a <;> fin_cases b <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [pauli, epsilon3, Matrix.mul_apply, Fin.sum_univ_two,
        Fin.sum_univ_three, Matrix.smul_apply, Matrix.sub_apply,
        Complex.I_mul_I, Complex.I_sq] <;> ring_nf <;> norm_num [Complex.I_sq]


/-- Scale of the orthonormal SU(2) color basis Tₐ = σₐ / √2. -/
def pauliScale : ℝ := Real.sqrt 2 / 2

lemma pauliScale_sq : pauliScale ^ 2 = (1/2 : ℝ) := by
  dsimp [pauliScale]
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma pauliScale_mul_sqrt : pauliScale * Real.sqrt 2 = 1 := by
  dsimp [pauliScale]
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  calc
    (Real.sqrt 2 / 2) * Real.sqrt 2 =
        (Real.sqrt 2) ^ 2 / 2 := by ring
    _ = 1 := by rw [hs]; norm_num

def normalizedPauli (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  (pauliScale : ℂ) • pauli a

/-- Trace orthogonality of the unnormalized Pauli basis. -/
lemma pauli_trace_zero (a : Fin 3) : Matrix.trace (pauli a) = 0 := by
  fin_cases a <;> norm_num [pauli, Matrix.trace, Fin.sum_univ_two]

lemma pauli_trace_pair (a b : Fin 3) :
    Matrix.trace (pauli a * pauli b) =
      (if a = b then 2 else 0 : ℂ) := by
  fin_cases a <;> fin_cases b <;>
    norm_num [pauli, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.I_sq]

/-- The scaled basis is trace-orthonormal, as required by AlgebraData 2. -/
lemma normalizedPauli_trace_pair (a b : Fin 3) :
    Matrix.trace (normalizedPauli a * normalizedPauli b) =
      (if a = b then 1 else 0 : ℂ) := by
  have hs : (pauliScale : ℂ) ^ 2 = (1/2 : ℂ) := by
    simpa using congrArg (fun t : ℝ => (t : ℂ)) pauliScale_sq
  have hprod : normalizedPauli a * normalizedPauli b =
      ((pauliScale : ℂ)^2) • (pauli a * pauli b) := by
    simp only [normalizedPauli, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, pow_two]
  rw [hprod, Matrix.trace_smul, smul_eq_mul, pauli_trace_pair, hs]
  split_ifs <;> norm_num

/-- The normalized Pauli basis has the manuscript's √2 structure constants. -/
lemma normalizedPauli_commutator (a b : Fin 3) :
    normalizedPauli a * normalizedPauli b -
        normalizedPauli b * normalizedPauli a =
      (Complex.I * (Real.sqrt 2 : ℂ)) •
        (∑ c : Fin 3, (epsilon3 a b c : ℂ) • normalizedPauli c) := by
  have hsq : (pauliScale : ℂ) ^ 2 = (1/2 : ℂ) := by
    simpa using congrArg (fun t : ℝ => (t : ℂ)) pauliScale_sq
  have hroot : (pauliScale : ℂ) * (Real.sqrt 2 : ℂ) = 1 := by
    simpa using congrArg (fun t : ℝ => (t : ℂ)) pauliScale_mul_sqrt
  have hscale : (pauliScale : ℂ) ^ 2 * (2 * Complex.I) =
      (Complex.I * (Real.sqrt 2 : ℂ)) * (pauliScale : ℂ) := by
    rw [hsq]
    calc
      (1/2 : ℂ) * (2 * Complex.I) = Complex.I := by ring
      _ = Complex.I * ((pauliScale : ℂ) * (Real.sqrt 2 : ℂ)) := by
        rw [hroot, mul_one]
      _ = (Complex.I * (Real.sqrt 2 : ℂ)) * (pauliScale : ℂ) := by ring
  have hprod (a b : Fin 3) : normalizedPauli a * normalizedPauli b =
      ((pauliScale : ℂ)^2) • (pauli a * pauli b) := by
    simp only [normalizedPauli, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, pow_two]
  have hsum :
      (∑ c : Fin 3, (epsilon3 a b c : ℂ) • normalizedPauli c) =
        (pauliScale : ℂ) • (∑ c : Fin 3, (epsilon3 a b c : ℂ) • pauli c) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro c _
    simp only [normalizedPauli]
    exact smul_comm (epsilon3 a b c : ℂ) (pauliScale : ℂ) (pauli c)
  calc
    _ = ((pauliScale : ℂ)^2) •
          (pauli a * pauli b - pauli b * pauli a) := by
            rw [hprod a b, hprod b a, smul_sub]
    _ = ((pauliScale : ℂ)^2 * (2 * Complex.I)) •
          (∑ c : Fin 3, (epsilon3 a b c : ℂ) • pauli c) := by
            rw [pauli_commutator, smul_smul]
    _ = (Complex.I * (Real.sqrt 2 : ℂ)) •
          (∑ c : Fin 3, (epsilon3 a b c : ℂ) • normalizedPauli c) := by
            rw [hsum, smul_smul, hscale]


/-- The explicit 2×2 Pauli matrices are Hermitian. -/
lemma pauli_hermitian (a : Fin 3) : (pauli a).IsHermitian := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.conjTranspose_apply, Complex.conj_I]

/-- The orthonormal Pauli color generators are Hermitian. -/
lemma normalizedPauli_hermitian (a : Fin 3) :
    (normalizedPauli a).IsHermitian := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [normalizedPauli, pauli, Matrix.conjTranspose_apply,
      Matrix.smul_apply, smul_eq_mul,
      Complex.conj_I, Complex.conj_ofReal]

/-- Normalization preserves the traceless color-generator condition. -/
lemma normalizedPauli_trace_zero (a : Fin 3) :
    Matrix.trace (normalizedPauli a) = 0 := by
  simp [normalizedPauli, Matrix.trace_smul, pauli_trace_zero]

/-- The 3-color orientation is invariant under a cyclic index permutation. -/
lemma epsilon3_cyclic (a b c : Fin 3) :
    epsilon3 a b c = epsilon3 b c a := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

/-- The normalized Pauli bracket in the exact Hermitian BFSS sign convention. -/
lemma normalizedPauli_realBracket (a b : Fin 3) :
    (-Complex.I) •
      (normalizedPauli a * normalizedPauli b -
        normalizedPauli b * normalizedPauli a) =
      (Real.sqrt 2 : ℂ) •
        (∑ c : Fin 3, (epsilon3 a b c : ℂ) • normalizedPauli c) := by
  rw [normalizedPauli_commutator, smul_smul]
  have h : (-Complex.I) * (Complex.I * (Real.sqrt 2 : ℂ)) =
      (Real.sqrt 2 : ℂ) := by
    calc
      (-Complex.I) * (Complex.I * (Real.sqrt 2 : ℂ)) =
          -(Complex.I ^ 2) * (Real.sqrt 2 : ℂ) := by ring
      _ = (Real.sqrt 2 : ℂ) := by rw [Complex.I_sq]; ring
  rw [h]


/--
A direct trace extraction identity: the normalized Pauli trace pairing
reads off the A-th coefficient of an epsilon-weighted color combination.
-/
lemma normalizedPauli_trace_epsilon_sum (a b c : Fin 3) :
    Matrix.trace (normalizedPauli a *
        (∑ d : Fin 3, (epsilon3 b c d : ℂ) • normalizedPauli d)) =
      (epsilon3 b c a : ℂ) := by
  rw [Matrix.mul_sum, Matrix.trace_sum]
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    normalizedPauli_trace_pair]
  simp [mul_ite]

/--
Fully concrete version of the color structure-constant trace formula,
in the sign and cyclic ordering of OpenAI's BFSS AlgebraData.
-/
lemma normalizedPauli_structureConstant_trace (a b c : Fin 3) :
    (Matrix.trace (normalizedPauli a *
      ((-Complex.I) •
        (normalizedPauli b * normalizedPauli c -
          normalizedPauli c * normalizedPauli b)))).re =
        Real.sqrt 2 * epsilon3 a b c := by
  rw [normalizedPauli_realBracket, Matrix.mul_smul, Matrix.trace_smul,
    normalizedPauli_trace_epsilon_sum]
  simp only [smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [epsilon3_cyclic a b c]

/--
An explicitly conditional, actual-upstream-API statement.
The hypothesis identifies the color basis; this theorem does not
construct an inhabitant of AlgebraData 2 or prove realizability.
-/
lemma algebraData_structureConstant_of_pauli_color
    (M : OAI.BFSSQuantum.AlgebraData 2)
    (hcolor : ∀ a : OAI.BFSSQuantum.ColorIndex 2,
      M.color a = normalizedPauli a)
    (a b c : OAI.BFSSQuantum.ColorIndex 2) :
    M.structureConstant a b c = Real.sqrt 2 * epsilon3 a b c := by
  change
    (Matrix.trace (M.color a *
      ((-Complex.I) • (M.color b * M.color c -
        M.color c * M.color b)))).re = _
  rw [hcolor a, hcolor b, hcolor c]
  exact normalizedPauli_structureConstant_trace a b c


/-- Squared norm of the three color minors for a pair of 3-vectors. -/
def colorWedgeSquared (u v : Fin 3 → ℝ) : ℝ :=
  (u 0 * v 1 - u 1 * v 0)^2 +
  (u 0 * v 2 - u 2 * v 0)^2 +
  (u 1 * v 2 - u 2 * v 1)^2

/--
Under an explicitly identified Pauli color basis, the *actual upstream*
coordinateBracket is the normalized cross product at any spatial pair.
This is conditional on AlgebraData 2; no concrete instance is asserted.
-/
lemma coordinateBracket_of_pauli_color
    (M : OAI.BFSSQuantum.AlgebraData 2)
    (hcolor : ∀ a : OAI.BFSSQuantum.ColorIndex 2,
      M.color a = normalizedPauli a)
    (x : OAI.BFSSQuantum.Boson 2)
    (p : OAI.BFSSGamma.SpatialPair)
    (a : OAI.BFSSQuantum.ColorIndex 2) :
    M.coordinateBracket x p a =
      Real.sqrt 2 * colorCross
        (fun b : Fin 3 => x (p.1.1,b))
        (fun c : Fin 3 => x (p.1.2,c)) a := by
  change (∑ b : OAI.BFSSQuantum.ColorIndex 2,
    ∑ c : OAI.BFSSQuantum.ColorIndex 2,
      M.structureConstant a b c * x (p.1.1,b) * x (p.1.2,c)) = _
  simp_rw [algebraData_structureConstant_of_pauli_color M hcolor]
  exact epsilon3_contraction _ _ a

/--
The pinned deformed BFSS potential at (h,m)=(1,0) is the sum of the
three squared color minors over strict spatial pairs, conditional on the
explicit normalized Pauli color basis.
-/
lemma deformedBosonicPotential_one_zero_eq_wedge
    (M : OAI.BFSSQuantum.AlgebraData 2)
    (hcolor : ∀ a : OAI.BFSSQuantum.ColorIndex 2,
      M.color a = normalizedPauli a)
    (x : OAI.BFSSQuantum.Boson 2) :
    M.deformedBosonicPotential 1 0 x =
      ∑ p : OAI.BFSSGamma.SpatialPair,
        colorWedgeSquared
          (fun a : Fin 3 => x (p.1.1,a))
          (fun a : Fin 3 => x (p.1.2,a)) := by
  have hshift (p : OAI.BFSSGamma.SpatialPair)
      (a : OAI.BFSSQuantum.ColorIndex 2) :
      OAI.BFSSGamma.shiftedPair 1 0
        (fun q => M.coordinateBracket x q a)
        (fun i => x (i,a)) p =
        -M.coordinateBracket x p a := by
    simp [OAI.BFSSGamma.shiftedPair]
  unfold OAI.BFSSQuantum.AlgebraData.deformedBosonicPotential
  simp only [hshift, zero_mul, neg_sq,
    zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, add_zero]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [coordinateBracket_of_pauli_color M hcolor x p]
  -- The upstream ColorIndex 2 is definitionally Fin 3, but the generic
  -- finite-sum rewrite does not recognize its unreduced index expression.
  -- Expose the actual three-component sum before using Fin.sum_univ_three.
  change (1/2 : ℝ) * (∑ a : Fin 3,
      (Real.sqrt 2 * colorCross
        (fun b : Fin 3 => x (p.1.1,b))
        (fun c : Fin 3 => x (p.1.2,c)) a)^2) =
      colorWedgeSquared
        (fun b : Fin 3 => x (p.1.1,b))
        (fun c : Fin 3 => x (p.1.2,c))
  rw [Fin.sum_univ_three]
  simp only [colorCross, colorWedgeSquared, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring


/--
The already-proven Pauli basis in openai/math uses color labels 1,2,3,
after its scalar identity element 0. Our color ordering agrees exactly.
-/
lemma pauli_eq_native_pauli (a : Fin 3) :
    pauli a = OAI.KirchbergRordam.Pauli.e a.succ := by
  fin_cases a <;>
    norm_num [pauli, OAI.KirchbergRordam.Pauli.e]

/--
An initial spanning milestone **over ℂ**: every traceless complex 2×2
matrix is a complex linear combination of our three Pauli colors.
This deliberately does NOT discharge the real-coefficient spanning field
required for *Hermitian* color matrices in BFSS AlgebraData 2.
-/
lemma nativePauli_complex_span_traceless
    (X : Matrix (Fin 2) (Fin 2) ℂ)
    (htrace : Matrix.trace X = 0) :
    X = ∑ a : Fin 3,
      OAI.KirchbergRordam.Pauli.coeff a.succ X • pauli a := by
  have hzero : OAI.KirchbergRordam.Pauli.coeff 0 X = 0 := by
    simp [OAI.KirchbergRordam.Pauli.coeff_apply,
      OAI.KirchbergRordam.Pauli.e_zero, htrace]
  calc
    X = ∑ a : Fin 4,
        OAI.KirchbergRordam.Pauli.coeff a X •
          OAI.KirchbergRordam.Pauli.e a :=
      (OAI.KirchbergRordam.Pauli.coeff_sum X).symm
    _ = ∑ a : Fin 3,
        OAI.KirchbergRordam.Pauli.coeff a.succ X •
          OAI.KirchbergRordam.Pauli.e a.succ := by
      rw [Fin.sum_univ_succ]
      simp [hzero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← pauli_eq_native_pauli a]


/--
The native Pauli coefficient of a Hermitian matrix is real. This is a
non-circular proof: the trace of a product of two Hermitian matrices is
real by adjoint reversal and cyclicity, rather than by color_spanning.
-/
lemma nativePauli_coeff_im_zero
    (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.IsHermitian)
    (a : Fin 3) :
    (OAI.KirchbergRordam.Pauli.coeff a.succ X).im = 0 := by
  have hstar : star (Matrix.trace (pauli a * X)) =
      Matrix.trace (pauli a * X) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      (pauli_hermitian a).eq, hX.eq, Matrix.trace_mul_comm]
  have ht : (Matrix.trace (pauli a * X)).im = 0 :=
    Complex.conj_eq_iff_im.mp (by simpa only [Complex.star_def] using hstar)
  rw [OAI.KirchbergRordam.Pauli.coeff_apply, ← pauli_eq_native_pauli a]
  simp [Complex.mul_im, ht]

/--
Discharge the precise real-coefficient Pauli color-spanning field of
OAI.BFSSQuantum.AlgebraData 2. This is a property of an explicit color
basis, not a constructed instance of the full BFSS algebra.
-/
lemma normalizedPauli_color_spanning
    (X : OAI.BFSSQuantum.ColorMatrix 2)
    (hX : X.IsHermitian) (htrace : Matrix.trace X = 0) :
    ∃ a : OAI.BFSSQuantum.ColorIndex 2 → ℝ,
      X = ∑ A, (a A : ℂ) • normalizedPauli A := by
  let c : Fin 3 → ℂ :=
    fun a => OAI.KirchbergRordam.Pauli.coeff a.succ X
  refine ⟨fun a => Real.sqrt 2 * (c a).re, ?_⟩
  change X = ∑ a : Fin 3,
    ((Real.sqrt 2 * (c a).re : ℝ) : ℂ) • normalizedPauli a
  have hroot : (pauliScale : ℂ) * (Real.sqrt 2 : ℂ) = 1 := by
    simpa using congrArg (fun t : ℝ => (t : ℂ)) pauliScale_mul_sqrt
  have hs : (Real.sqrt 2 : ℂ) * (pauliScale : ℂ) = 1 := by
    calc
      _ = (pauliScale : ℂ) * (Real.sqrt 2 : ℂ) := by ring
      _ = 1 := hroot
  calc
    X = ∑ a : Fin 3, c a • pauli a :=
      nativePauli_complex_span_traceless X htrace
    _ = ∑ a : Fin 3,
        ((Real.sqrt 2 * (c a).re : ℝ) : ℂ) • normalizedPauli a := by
      apply Finset.sum_congr rfl
      intro a _
      have hc : c a = ((c a).re : ℂ) := by
        apply Complex.ext
        · simp
        · simpa only [Complex.ofReal_im] using
            (nativePauli_coeff_im_zero X hX a)
      have heq :
          (Real.sqrt 2 : ℂ) * ((c a).re : ℂ) * (pauliScale : ℂ) =
            ((c a).re : ℂ) := by
        calc
          _ = ((c a).re : ℂ) *
                ((Real.sqrt 2 : ℂ) * (pauliScale : ℂ)) := by ring
          _ = _ := by rw [hs, mul_one]
      calc
        c a • pauli a = ((c a).re : ℂ) • pauli a := by
          rw [hc]
          simp only [Complex.ofReal_re]
        _ = ((Real.sqrt 2 * (c a).re : ℝ) : ℂ) • normalizedPauli a := by
          simp only [normalizedPauli, smul_smul, Complex.ofReal_mul]
          rw [heq]


/--
The complete four-field SU(2) color slice of the pinned BFSS AlgebraData
requirements has an explicit inhabitant, independently of gamma/theta.
This is NOT a construction of AlgebraData 2.
-/
theorem exists_normalizedPauli_color_basis :
    ∃ C : OAI.BFSSQuantum.ColorIndex 2 →
        OAI.BFSSQuantum.ColorMatrix 2,
      (∀ A, (C A).IsHermitian) ∧
      (∀ A, Matrix.trace (C A) = 0) ∧
      (∀ A B, Matrix.trace (C A * C B) =
        if A = B then 1 else 0) ∧
      (∀ X : OAI.BFSSQuantum.ColorMatrix 2,
        X.IsHermitian → Matrix.trace X = 0 →
          ∃ a : OAI.BFSSQuantum.ColorIndex 2 → ℝ,
            X = ∑ A, (a A : ℂ) • C A) := by
  refine ⟨normalizedPauli, normalizedPauli_hermitian,
    normalizedPauli_trace_zero, normalizedPauli_trace_pair, ?_⟩
  intro X hX htrace
  exact normalizedPauli_color_spanning X hX htrace

#print axioms exists_normalizedPauli_color_basis

#print axioms nativePauli_coeff_im_zero
#print axioms normalizedPauli_color_spanning

#print axioms pauli_eq_native_pauli
#print axioms nativePauli_complex_span_traceless

#print axioms coordinateBracket_of_pauli_color
#print axioms deformedBosonicPotential_one_zero_eq_wedge

#print axioms normalizedPauli_trace_epsilon_sum
#print axioms normalizedPauli_structureConstant_trace
#print axioms algebraData_structureConstant_of_pauli_color

#print axioms pauli_hermitian
#print axioms normalizedPauli_hermitian
#print axioms normalizedPauli_trace_zero
#print axioms epsilon3_cyclic
#print axioms normalizedPauli_realBracket

#print axioms pauliScale_sq
#print axioms pauli_trace_pair
#print axioms normalizedPauli_trace_pair
#print axioms normalizedPauli_commutator

#print axioms pauli_commutator

#print axioms epsilon3_contraction
#print axioms normalized_cross_energy

end
end FCP.BFSSSU2

/-!
Independent BFSS SU(2) formalization contribution by Evan T. Kotler (2026).
Research DOI: https://doi.org/10.5281/zenodo.23291242
FCP source: b60baa806dab3f0b296229a78f70e07b787544ab, experiments/openai-math-su2-concrete-potential/SU2ColorCrossProbe.lean
Copyright (c) 2026 Evan T. Kotler. SPDX-License-Identifier: Apache-2.0.
Build status: integrated candidate; upstream port NOT YET independently verified.
OpenAI retains credit for the original BFSS definitions on which this work builds.
-/
