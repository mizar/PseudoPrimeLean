/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelSquare
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-! # Rational absolute mass of the high Gaussian kernels -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Real and scaled imaginary polynomial parts of the power of `a + it`,
in the variable `u = a² + t²`. -/
private noncomputable def powerParts (a : ℚ) : ℕ → Polynomial ℚ × Polynomial ℚ
  | 0 => (1, 0)
  | k + 1 =>
    let (A, B) := powerParts a k
    (Polynomial.C a * A + (Polynomial.C (a ^ 2) - Polynomial.X) * B, A + Polynomial.C a * B)

/-- Evaluating the two polynomial parts recovers the complex power. -/
private theorem power_parts_eval (a : ℚ) (t : ℝ) (k : ℕ) :
    let u := (a : ℝ) ^ 2 + t ^ 2
    let (A, B) := powerParts a k
    ((A.eval₂ (Rat.castHom ℝ) u : ℝ) : ℂ) +
        (Complex.I * (t : ℂ)) * ((B.eval₂ (Rat.castHom ℝ) u : ℝ) : ℂ) =
      (Complex.I * (t : ℂ) + (a : ℂ)) ^ k := by
  induction k with
  | zero =>
    simp only [powerParts, Polynomial.eval₂_one, Polynomial.eval₂_zero, Complex.ofReal_one,
      Complex.ofReal_zero, mul_zero, add_zero, pow_zero]
  | succ k ih =>
    rcases h : powerParts a k with ⟨A, B⟩
    rw [h] at ih
    rw [powerParts, h]
    dsimp only at ih ⊢
    rw [pow_succ (Complex.I * (t : ℂ) + (a : ℂ)) k, ← ih]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_C,
      Polynomial.eval₂_X, Rat.coe_castHom, Rat.cast_pow, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_ratCast]
    linear_combination
      (-(t : ℂ) ^ 2 * (B.eval₂ (Rat.castHom ℝ) ((a : ℝ) ^ 2 + t ^ 2) : ℝ)) * Complex.I_sq

/-- The real and scaled imaginary parts of a rational polynomial on the vertical line. -/
private noncomputable def polynomialParts (a : ℚ) (P : Polynomial ℚ) :
    Polynomial ℚ × Polynomial ℚ :=
  (∑ k ∈ Finset.range (P.natDegree + 1), Polynomial.C (P.coeff k) * (powerParts a k).1,
    ∑ k ∈ Finset.range (P.natDegree + 1), Polynomial.C (P.coeff k) * (powerParts a k).2)

/-- Recombine the two parts by summing the monomial identity. -/
private theorem polynomial_parts_eval (a : ℚ) (P : Polynomial ℚ) (t : ℝ) :
    let u := (a : ℝ) ^ 2 + t ^ 2
    let A := (polynomialParts a P).1
    let B := (polynomialParts a P).2
    ((A.eval₂ (Rat.castHom ℝ) u : ℝ) : ℂ) +
        (Complex.I * (t : ℂ)) * ((B.eval₂ (Rat.castHom ℝ) u : ℝ) : ℂ) =
      P.eval₂ (Rat.castHom ℂ) (Complex.I * (t : ℂ) + (a : ℂ)) := by
  dsimp only [polynomialParts]
  rw [Polynomial.eval₂_eq_sum_range (p := P)]
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C, Rat.coe_castHom,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_ratCast, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_left_comm (P.coeff k : ℂ), ← mul_add]
  congr 1
  exact power_parts_eval a t k

/-- For a rational polynomial `P`, this polynomial in `u = a² + t²` represents
the squared norm of `P(a + it)`. The imaginary part contributes `(u - a²) B²`. -/
public noncomputable def normSqPolynomial (a : ℚ) (P : Polynomial ℚ) : Polynomial ℚ :=
  let (A, B) := polynomialParts a P
  A ^ 2 + (Polynomial.X - Polynomial.C (a ^ 2)) * B ^ 2

/-- Evaluating the rational norm-square polynomial on the vertical line recovers
the absolute numerator in the high Gaussian mass. -/
public theorem norm_sq_polynomial_eval (a : ℚ) (P : Polynomial ℚ) (t : ℝ) :
    (normSqPolynomial a P).eval₂ (Rat.castHom ℝ) ((a : ℝ) ^ 2 + t ^ 2) =
      ‖P.eval₂ (Rat.castHom ℂ) (Complex.I * (t : ℂ) + (a : ℂ))‖ ^ 2 := by
  rw [← polynomial_parts_eval a P t, Complex.sq_norm, Complex.normSq_apply]
  simp only [normSqPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_mul,
    Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, Rat.coe_castHom, Rat.cast_pow,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The critical-line absolute value is a rational function of
`u = (K.pole : ℝ)² + t²`, with the polynomial numerator used in the mass transform. -/
public theorem high_gaussian_norm_rational (K : HighGaussianKernel) (t : ℝ) :
    ‖∑ j ∈ Finset.range (2 * K.degree + 1),
          (K.expandedCoeff j : ℂ) * Complex.exp (5 * (Complex.I * (t : ℂ))) /
            (Complex.I * (t : ℂ) + (K.pole : ℂ)) ^ (K.logPower j + 1)‖ =
      let u := (K.pole : ℝ) ^ 2 + t ^ 2
      (K.normalization : ℝ) * (normSqPolynomial K.pole K.polynomial).eval₂ (Rat.castHom ℝ) u /
        u ^ (K.degree + 2) := by
  rw [high_gaussian_kernel_norm, ← norm_sq_polynomial_eval]
  have hn : ‖Complex.I * (t : ℂ) + (K.pole : ℂ)‖ ^ 2 = (K.pole : ℝ) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [← Complex.ofReal_ratCast, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [show 2 * K.degree + 4 = 2 * (K.degree + 2) by ring, pow_mul, hn]

/-- A common bound for twice the degrees also bounds the degree of the sum. -/
private theorem add_degree_twice {A B : Polynomial ℚ} {n : ℕ} (ha : 2 * A.natDegree ≤ n)
    (hb : 2 * B.natDegree ≤ n) : 2 * (A + B).natDegree ≤ n := by
  apply (Nat.mul_le_mul_left 2 (Polynomial.natDegree_add_le A B)).trans
  rw [← Nat.mul_max_mul_left]
  exact max_le ha hb

/-- The powers of `a + it` have degree at most their exponent when the variable
`u` has weight two and the imaginary factor has weight one. -/
private theorem power_parts_degree (a : ℚ) (k : ℕ) :
    2 * (powerParts a k).1.natDegree ≤ k ∧
      ((powerParts a k).2 = 0 ∨ 2 * (powerParts a k).2.natDegree + 1 ≤ k) := by
  induction k with
  | zero => simp only [powerParts, Polynomial.natDegree_one, mul_zero, le_refl, true_or, and_self]
  | succ k ih =>
    rcases h : powerParts a k with ⟨A, B⟩
    rw [h] at ih
    rcases ih with ⟨ha, hb⟩
    rw [powerParts, h]
    dsimp only at ha hb ⊢
    have hA :=
      (Nat.mul_le_mul_left 2 (Polynomial.natDegree_C_mul_le a A)).trans (ha.trans (Nat.le_succ k))
    have hB : 2 * ((Polynomial.C (a ^ 2) - Polynomial.X) * B).natDegree ≤ k + 1 := by
      rcases hb with hB | hB
      · simp only [hB, mul_zero, Polynomial.natDegree_zero, Nat.zero_le]
      have hmul := Polynomial.natDegree_mul_le (p := Polynomial.C (a ^ 2) - Polynomial.X) (q := B)
      have hsub : (Polynomial.C (a ^ 2) - Polynomial.X).natDegree = 1 := by
        rw [← neg_sub (Polynomial.X : Polynomial ℚ) (Polynomial.C (a ^ 2)),
          Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
      rw [hsub] at hmul
      linarith only [hmul, hB]
    refine ⟨add_degree_twice hA hB, Or.inr ?_⟩
    have hb' : 2 * B.natDegree ≤ k := by
      rcases hb with hB | hB
      · simp only [hB, Polynomial.natDegree_zero, mul_zero, Nat.zero_le]
      · exact (Nat.le_succ _).trans hB
    have hadd :=
      add_degree_twice ha ((Nat.mul_le_mul_left 2 (Polynomial.natDegree_C_mul_le a B)).trans hb')
    exact Nat.add_le_add_right hadd 1

/-- Multiplication by a rational constant and finite summation preserve a common degree bound. -/
private theorem sum_degree_twice {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℚ) {n : ℕ}
    (hf : ∀ i ∈ s, 2 * (f i).natDegree ≤ n) : 2 * (∑ i ∈ s, f i).natDegree ≤ n := by
  have h2 : 0 < (2 : ℕ) := by decide
  have hs : (∑ i ∈ s, f i).natDegree ≤ n / 2 :=
    Polynomial.natDegree_sum_le_of_forall_le s f fun i hi ↦
      (Nat.le_div_iff_mul_le h2).mpr
        (by
          rw [Nat.mul_comm]; exact hf i hi)
  simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le h2).mp hs

/-- The real and scaled imaginary polynomials have weighted degree at most `N`. -/
private theorem polynomial_parts_degree (a : ℚ) (P : Polynomial ℚ) {N : ℕ} (hP : P.natDegree ≤ N) :
    2 * (polynomialParts a P).1.natDegree ≤ N ∧ 2 * (polynomialParts a P).2.natDegree ≤ N - 1 := by
  unfold polynomialParts
  constructor
  · apply sum_degree_twice
    intro i hi
    exact
      (Nat.mul_le_mul_left 2 (Polynomial.natDegree_C_mul_le _ _)).trans
        ((power_parts_degree a i).1.trans ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hP))
  · apply sum_degree_twice
    intro i hi
    have hle : i ≤ N := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hP
    apply (Nat.mul_le_mul_left 2 (Polynomial.natDegree_C_mul_le _ _)).trans
    rcases (power_parts_degree a i).2 with h | h
    · simp only [h, Polynomial.natDegree_zero, mul_zero, Nat.zero_le]
    · exact Nat.le_sub_of_add_le (h.trans hle)

/-- If `P` has degree at most `N ≥ 1`, its squared norm in the variable
`u = a² + t²` has degree at most `N`. -/
public theorem norm_sq_polynomial_degree (a : ℚ) (P : Polynomial ℚ) {N : ℕ} (hN : 1 ≤ N)
    (hP : P.natDegree ≤ N) : (normSqPolynomial a P).natDegree ≤ N := by
  obtain ⟨ha, hb⟩ := polynomial_parts_degree a P hP
  unfold normSqPolynomial
  dsimp only
  apply Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_pow_le.trans ha)
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_X_sub_C]
  exact
    (Nat.add_le_add_left (Polynomial.natDegree_pow_le.trans hb) 1).trans_eq
      ((Nat.add_comm 1 _).trans (Nat.sub_add_cancel hN))

/-- The absolute kernel is a finite signed sum of reciprocal quadratic powers,
all of order at least two. This is the input to the mass Fourier transform. -/
public theorem high_gaussian_norm_reciprocal (K : HighGaussianKernel) (t : ℝ) :
    ‖∑ j ∈ Finset.range (2 * K.degree + 1),
          (K.expandedCoeff j : ℂ) * Complex.exp (5 * (Complex.I * (t : ℂ))) /
            (Complex.I * (t : ℂ) + (K.pole : ℂ)) ^ (K.logPower j + 1)‖ =
      ∑ j ∈ Finset.range (K.degree + 1),
        (K.normalization : ℝ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℝ) /
          ((K.pole : ℝ) ^ 2 + t ^ 2) ^ (K.degree + 2 - j) := by
  have hd : 1 ≤ K.degree := by cases K <;> decide
  have hp := norm_sq_polynomial_degree K.pole K.polynomial hd (high_gaussian_polynomial_degree K)
  have ha := (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  let u : ℝ := (K.pole : ℝ) ^ 2 + t ^ 2
  have hu : u ≠ 0 := (add_pos_of_pos_of_nonneg (pow_pos ha 2) (sq_nonneg t)).ne'
  rw [high_gaussian_norm_rational]
  change
    (K.normalization : ℝ) * (normSqPolynomial K.pole K.polynomial).eval₂ (Rat.castHom ℝ) u /
        u ^ (K.degree + 2) =
      _
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hp)]
  simp only [Rat.coe_castHom, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ K.degree + 2 :=
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans (Nat.le_add_right _ _)
  have he : u ^ j / u ^ (K.degree + 2) = 1 / u ^ (K.degree + 2 - j) := by
    apply (div_eq_div_iff (pow_ne_zero _ hu) (pow_ne_zero _ hu)).mpr
    rw [← pow_add, Nat.add_comm j, Nat.sub_add_cancel hj', one_mul]
  rw [← mul_assoc, mul_div_assoc, he, mul_one_div]

end PseudoPrime.PrimeTestBounds.MillerRabin
