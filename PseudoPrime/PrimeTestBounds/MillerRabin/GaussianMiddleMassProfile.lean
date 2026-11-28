/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassExtension
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianBalancedPoleKernel
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianOppositePolePolynomial
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassExtension

/-! # Rational Fourier profiles for the middle Gaussian mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational polynomial factor of the middle mass profile.
The normalization and the common exponential are applied separately. -/
public noncomputable def middleMassPolynomial (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (d + 1),
    Polynomial.C ((normSqPolynomial a Q).coeff j) * oppositePolePolynomial a (d + 2 - j) (d + 2 - j)

/-- For each balanced component, Mellin inversion at zero equals the
Fourier expression in the absolute logarithm. -/
private theorem middle_balanced_profile_log (a : ℚ) (ha : 2 ≤ (a : ℝ)) (m : ℕ) (hm : 0 < m) {u : ℝ}
    (hu : 0 < u) :
    k131SymmetricProfile a m m u =
      Real.exp (-(a : ℝ) * |Real.log u|) *
        (oppositePolePolynomial a m m).eval₂ (Rat.castHom ℝ) |Real.log u| := by
  have ha₀ := (by norm_num only : (0 : ℝ) < 2).trans_le ha
  have h := balanced_pole_inverse ha (m - 1) (c := 0) (neg_lt_zero.mpr ha₀) ha₀ hu
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hphase (t : ℝ) :
    (u : ℂ) ^ (-(Complex.I * (t : ℂ))) = Complex.exp (((-Real.log u * t : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), ← Complex.ofReal_log hu.le,
      Complex.ofReal_mul, Complex.ofReal_neg]
    congr 1
    ring
  have hdist (t : ℝ) :
    (((a : ℝ) : ℂ)) ^ 2 - (Complex.I * (t : ℂ)) ^ 2 = (((a : ℝ) ^ 2 + t ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_pow, mul_pow, Complex.I_sq, neg_one_mul,
      sub_neg_eq_add]
  unfold Analysis.inverseMellin at h
  simp only [Complex.ofReal_zero, zero_add, hphase, balanced_pole_function, hm', hdist,
    mul_comm (1 / _ : ℂ) (Complex.exp _), mul_one_div] at h
  rw [cauchy_fourier_polynomial a ((by norm_num only : (1 : ℝ) ≤ 2).trans ha) m hm
      (-Real.log u)] at h
  have hr := Complex.ofReal_injective (by simpa only [← Complex.ofReal_mul, abs_neg] using h)
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp (disch := exact hp) at hr
  simp only [neg_mul]
  linarith only [hr]

/-- At a positive argument the mass profile is half the common exponential
times the rational Fourier polynomial. -/
public theorem middle_mass_profile_log (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) (ha : 2 ≤ (a : ℝ)) {u : ℝ}
    (hu : 0 < u) :
    middleMassProfile Q a d u =
      1 / 2 * Real.exp (-(a : ℝ) * |Real.log u|) *
        (middleMassPolynomial Q a d).eval₂ (Rat.castHom ℝ) |Real.log u| := by
  simp only [middleMassProfile, middleMassPolynomial, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Rat.coe_castHom, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hm := Nat.sub_pos_of_lt (hj'.trans_lt (Nat.lt_add_of_pos_right (by decide : 0 < 2)))
  rw [middle_balanced_profile_log a ha _ hm hu]
  ring

/-- The central profile value is half the constant coefficient. -/
public theorem middle_mass_profile_one (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) (ha : 2 ≤ (a : ℝ)) :
    middleMassProfile Q a d 1 = ((middleMassPolynomial Q a d).coeff 0 : ℝ) / 2 := by
  rw [middle_mass_profile_log Q a d ha zero_lt_one]
  simp only [Real.log_one, abs_zero, mul_zero, Real.exp_zero, mul_one, Polynomial.eval₂_at_zero,
    Rat.coe_castHom]
  ring

/-- At positive integers, twice the weighted Mellin profile is the
Mangoldt weight times the mass polynomial and the decaying power. -/
private theorem middle_twice_mass_weight (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) (ha : 2 ≤ (a : ℝ))
    {n : ℕ} (hn : 0 < n) :
    2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n * middleMassProfile Q a d n) =
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(a : ℝ) - 1 / 2) *
        (middleMassPolynomial Q a d).eval₂ (Rat.castHom ℝ) (Real.log n) := by
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  rw [middle_mass_profile_log Q a d ha hn₀, abs_of_nonneg (Real.log_nonneg hn₁)]
  have he : Real.exp (-(a : ℝ) * Real.log n) = (n : ℝ) ^ (-(a : ℝ)) := by
    rw [Real.rpow_def_of_pos hn₀, mul_comm (Real.log n)]
  rw [he, Real.sqrt_eq_rpow, sub_eq_add_neg, Real.rpow_add hn₀]
  simp only [Real.rpow_neg hn₀.le]
  ring

/-- The cutoff tail in the three-character identity uses the same rational
polynomial as the conductor coefficient. -/
public theorem middle_mass_tail_polynomial (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) (ha : 2 ≤ (a : ℝ))
    (X : ℝ) (f : ℕ → ℝ) :
    2 *
        (∑' n : { n : ℕ // ⌊X⌋₊ < n },
          f n.val *
            (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
              middleMassProfile Q a d n.val)) =
      ∑' n : { n : ℕ // ⌊X⌋₊ < n },
        ArithmeticFunction.vonMangoldt n.val * f n.val * (n.val : ℝ) ^ (-(a : ℝ) - 1 / 2) *
          (middleMassPolynomial Q a d).eval₂ (Rat.castHom ℝ) (Real.log n.val) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [mul_left_comm (2 : ℝ),
    middle_twice_mass_weight Q a d ha ((Nat.zero_le _).trans_lt n.property)]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
