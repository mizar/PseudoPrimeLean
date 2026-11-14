/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCount100PhaseRH
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaFiniteEulerMaclaurin
import Mathlib.Analysis.Complex.Liouville

/-! # Derivative of the 127-term Dirichlet sum -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- An integer square-root lower approximation gives an upper bound for the
reciprocal square root of a positive natural number. -/
private theorem inv_sqrt_le_rat (n : ℕ) (hn : 1 ≤ n) :
    1 / Real.sqrt n ≤ (10 : ℝ) / Nat.sqrt (100 * n) := by
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hroot : (0 : ℝ) < (Nat.sqrt (100 * n) : ℝ) := by
    exact_mod_cast (Nat.sqrt_pos.mpr (Nat.mul_pos (by norm_num only) hnpos))
  have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
  have hsq : ((Nat.sqrt (100 * n) : ℕ) : ℝ) ^ 2 ≤ 100 * (n : ℝ) := by
    have hh := Nat.sqrt_le (100 * n)
    have hh' : (Nat.sqrt (100 * n) : ℝ) * (Nat.sqrt (100 * n) : ℝ) ≤ 100 * (n : ℝ) := by
      exact_mod_cast hh
    simpa only [pow_two] using hh'
  have hl : (Nat.sqrt (100 * n) : ℝ) / 10 ≤ Real.sqrt n := by
    apply (Real.le_sqrt (div_nonneg (Nat.cast_nonneg _) (by norm_num only)) (Nat.cast_nonneg _)).2
    nlinarith only [hsq]
  apply (div_le_div_iff₀ hsqrtn hroot).2
  nlinarith only [hl]

/-- The reciprocal square-root sum through 127 is below 22. The finite
comparison uses integer square roots and a kernel-checked rational inequality. -/
private theorem inv_sqrt_sum_lt : (∑ n ∈ Finset.Icc (1 : ℕ) 127, (1 : ℝ) / Real.sqrt n) < 22 := by
  have hr : (∑ n ∈ Finset.Icc (1 : ℕ) 127, (10 : ℚ) / Nat.sqrt (100 * n)) < 22 := by decide +kernel
  have hr' := (Rat.cast_lt (K := ℝ)).2 hr
  norm_num only [Rat.cast_sum, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hr'
  apply lt_of_le_of_lt ?_ hr'
  apply Finset.sum_le_sum
  intro n hn
  exact inv_sqrt_le_rat n (Finset.mem_Icc.mp hn).1

/-- A rational logarithm certificate places `log 128` below 5. -/
private theorem log_128_lt : Real.log 128 < 5 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 128 8 32 0 (48520303 / 10000000) = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  linarith only [h.2]

/-- The logarithmically weighted reciprocal square-root sum through 127 is
below 110. This bounds the derivative of the finite Dirichlet polynomial. -/
private theorem log_inv_sqrt_sum_lt :
    (∑ n ∈ Finset.Icc (1 : ℕ) 127, Real.log n / Real.sqrt n) < 110 := by
  have hcompare :
    (∑ n ∈ Finset.Icc (1 : ℕ) 127, Real.log n / Real.sqrt n) ≤
      ∑ n ∈ Finset.Icc (1 : ℕ) 127, (5 : ℝ) * (1 / Real.sqrt n) := by
    apply Finset.sum_le_sum
    intro n hn
    have hnle : (n : ℝ) ≤ 128 := by
      exact_mod_cast ((Finset.mem_Icc.mp hn).2.trans (by norm_num only : 127 ≤ 128))
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)
    have hl : Real.log n ≤ 5 := (Real.log_le_log hnpos hnle).trans log_128_lt.le
    have hd : 0 ≤ 1 / Real.sqrt n := div_nonneg (by norm_num only) (Real.sqrt_nonneg _)
    have hm := mul_le_mul_of_nonneg_right hl hd
    simpa only [mul_one_div] using hm
  rw [← Finset.mul_sum] at hcompare
  nlinarith only [hcompare, inv_sqrt_sum_lt]

/-- The squared-logarithm weighted reciprocal square-root sum through 127
is below 359. Three logarithm ranges and rational square-root bounds supply
the sharper estimate needed for eight-cell interpolation. -/
private theorem log_sq_inv_sqrt_sum_lt :
    (∑ n ∈ Finset.Icc (1 : ℕ) 127, (Real.log n) ^ 2 / Real.sqrt n) < 359 := by
  have h20 :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 20 5 32 0 3 = true from by decide +kernel)
  have h54 :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 54 6 32 0 4 = true from by decide +kernel)
  have h128 :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 128 8 32 0 5 = true from by decide +kernel)
  norm_num only [Rat.cast_ofNat] at h20 h54 h128
  have hr :
    (∑ n ∈ Finset.Icc (1 : ℕ) 127,
        (if n ≤ 20 then (9 : ℚ) else if n ≤ 54 then 16 else 25) * (10 / Nat.sqrt (100 * n))) <
      359 := by
    decide +kernel
  have hr' := (Rat.cast_lt (K := ℝ)).2 hr
  norm_num only [Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hr'
  apply lt_of_le_of_lt ?_ hr'
  apply Finset.sum_le_sum
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlog0 := Real.log_nonneg hn1R
  have hlog : (Real.log n) ^ 2 ≤ ((if n ≤ 20 then (9 : ℚ) else if n ≤ 54 then 16 else 25) : ℝ) := by
    split_ifs with h20n h54n
    · have hh := (Real.log_le_log hnpos (by exact_mod_cast h20n)).trans h20.2
      norm_num only [Rat.cast_ofNat]
      nlinarith only [hh, hlog0]
    · have hh := (Real.log_le_log hnpos (by exact_mod_cast h54n)).trans h54.2
      nlinarith only [hh, hlog0]
    · have hn128 : n ≤ 128 := (Finset.mem_Icc.mp hn).2.trans (by norm_num only)
      have hh := (Real.log_le_log hnpos (by exact_mod_cast hn128)).trans h128.2
      nlinarith only [hh, hlog0]
  have hnonneg : 0 ≤ ((if n ≤ 20 then (9 : ℚ) else if n ≤ 54 then 16 else 25) : ℝ) := by
    split_ifs <;> norm_num only [Rat.cast_ofNat]
  have hinv : 0 ≤ 1 / Real.sqrt n := div_nonneg (by norm_num only) (Real.sqrt_nonneg _)
  have hm := mul_le_mul hlog (inv_sqrt_le_rat n hn1) hinv hnonneg
  by_cases h20n : n ≤ 20
  · simpa only [ite_eq_left h20n, Rat.cast_ofNat, mul_one_div] using hm
  · by_cases h54n : n ≤ 54
    · simpa only [ite_eq_right h20n, ite_eq_left h54n, Rat.cast_ofNat, mul_one_div] using hm
    · simpa only [ite_eq_right h20n, ite_eq_right h54n, Rat.cast_ofNat, mul_one_div] using hm

/-- A three-range logarithm bound and rational square-root comparison put
the weighted reciprocal square-root sum through 127 below 90. -/
private theorem log_inv_sqrt_sum_lt_90 :
    (∑ n ∈ Finset.Icc (1 : ℕ) 127, Real.log n / Real.sqrt n) < 90 := by
  have h20 :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 20 5 32 0 3 = true from by decide +kernel)
  have h54 :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 54 6 32 0 4 = true from by decide +kernel)
  have h128 :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 128 8 32 0 5 = true from by decide +kernel)
  norm_num only [Rat.cast_ofNat] at h20 h54 h128
  have hr :
    (∑ n ∈ Finset.Icc (1 : ℕ) 127,
        (if n ≤ 20 then (3 : ℚ) else if n ≤ 54 then 4 else 5) * (10 / Nat.sqrt (100 * n))) <
      90 := by
    decide +kernel
  have hr' := (Rat.cast_lt (K := ℝ)).2 hr
  norm_num only [Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hr'
  apply lt_of_le_of_lt ?_ hr'
  apply Finset.sum_le_sum
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hlog : Real.log n ≤ ((if n ≤ 20 then (3 : ℚ) else if n ≤ 54 then 4 else 5) : ℝ) := by
    split_ifs with h20n h54n
    · exact (Real.log_le_log hnpos (by exact_mod_cast h20n)).trans h20.2
    · exact (Real.log_le_log hnpos (by exact_mod_cast h54n)).trans h54.2
    · have hn128 : n ≤ 128 := (Finset.mem_Icc.mp hn).2.trans (by norm_num only)
      exact (Real.log_le_log hnpos (by exact_mod_cast hn128)).trans h128.2
  have hnonneg : 0 ≤ ((if n ≤ 20 then (3 : ℚ) else if n ≤ 54 then 4 else 5) : ℝ) := by
    split_ifs <;> norm_num only [Rat.cast_ofNat]
  have hinv : 0 ≤ 1 / Real.sqrt n := div_nonneg (by norm_num only) (Real.sqrt_nonneg _)
  have hm := mul_le_mul hlog (inv_sqrt_le_rat n hn1) hinv hnonneg
  by_cases h20n : n ≤ 20
  · simpa only [ite_eq_left h20n, Rat.cast_ofNat, mul_one_div] using hm
  · by_cases h54n : n ≤ 54
    · simpa only [ite_eq_right h20n, ite_eq_left h54n, Rat.cast_ofNat, mul_one_div] using hm
    · simpa only [ite_eq_right h20n, ite_eq_right h54n, Rat.cast_ofNat, mul_one_div] using hm

/-- In the half-plane `Re s ≥ 1/2`, a positive integer raised to `-s`
has norm at most its reciprocal square root. -/
private theorem norm_cpow_neg_le (s : ℂ) (hs : (1 / 2 : ℝ) ≤ s.re) (n : ℕ) (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-s)‖ ≤ 1 / Real.sqrt n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num only) hn1
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by rfl, Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]
  calc
    (n : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hs)
    _ = 1 / Real.sqrt n := by
      rw [Real.rpow_neg (le_of_lt hn0), ← Real.sqrt_eq_rpow]
      exact (one_div _).symm

/-- Differentiate a finite Dirichlet sum whose indices are positive.
Each term is differentiated as a complex power with constant base. -/
private theorem hasDerivAt_dirichlet_sum (s : ℂ) (u : Finset ℕ) (hu : ∀ n ∈ u, 1 ≤ n) :
    HasDerivAt (fun z : ℂ => ∑ n ∈ u, (n : ℂ) ^ (-z))
      (∑ n ∈ u, -((Real.log n : ℂ) * (n : ℂ) ^ (-s))) s := by
  have hsum :
    HasDerivAt (∑ n ∈ u, fun z : ℂ => (n : ℂ) ^ (-z))
      (∑ n ∈ u, -((Real.log n : ℂ) * (n : ℂ) ^ (-s))) s := by
    apply HasDerivAt.sum
    intro n hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (hu n hn)
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
    have hd := ((hasDerivAt_id s).neg).const_cpow (Or.inl hn0)
    simpa only [Pi.neg_apply, id_eq, ← Complex.ofReal_natCast,
      ← Complex.ofReal_log (Nat.cast_nonneg n), mul_neg, mul_one, one_mul, neg_mul, mul_comm] using
      hd
  have heq : (∑ n ∈ u, fun z : ℂ => (n : ℂ) ^ (-z)) = (fun z : ℂ => ∑ n ∈ u, (n : ℂ) ^ (-z)) := by
    funext z
    simp only [Finset.sum_apply]
  rw [heq] at hsum
  exact hsum

/-- Differentiate the first derivative of a finite Dirichlet sum. Each
second derivative contributes the squared logarithm times the original power. -/
private theorem hasDerivAt_dirichlet_deriv (s : ℂ) (u : Finset ℕ) (hu : ∀ n ∈ u, 1 ≤ n) :
    HasDerivAt (fun z : ℂ => ∑ n ∈ u, -((Real.log n : ℂ) * (n : ℂ) ^ (-z)))
      (∑ n ∈ u, ((Real.log n : ℂ) ^ 2 * (n : ℂ) ^ (-s))) s := by
  have hsum :
    HasDerivAt (∑ n ∈ u, fun z : ℂ => -((Real.log n : ℂ) * (n : ℂ) ^ (-z)))
      (∑ n ∈ u, ((Real.log n : ℂ) ^ 2 * (n : ℂ) ^ (-s))) s := by
    apply HasDerivAt.sum
    intro n hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (hu n hn)
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
    have hd := (((hasDerivAt_id s).neg).const_cpow (Or.inl hn0)).const_mul (-(Real.log n : ℂ))
    have he :
      -(Real.log n : ℂ) * ((n : ℂ) ^ (-s) * Complex.log n * (-1)) =
        (Real.log n : ℂ) ^ 2 * (n : ℂ) ^ (-s) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
      ring
    simpa only [Pi.neg_apply, id_eq, neg_mul] using hd.congr_deriv he
  have heq :
    (∑ n ∈ u, fun z : ℂ => -((Real.log n : ℂ) * (n : ℂ) ^ (-z))) =
      (fun z : ℂ => ∑ n ∈ u, -((Real.log n : ℂ) * (n : ℂ) ^ (-z))) := by
    funext z
    simp only [Finset.sum_apply]
  rw [heq] at hsum
  exact hsum

/-- For `Re s ≥ 1/2`, the derivative of the Dirichlet sum over `1 ≤ n ≤ 127`
has norm strictly below 110. This is the finite-sum part of the proposed
Euler–Maclaurin derivative bound at height 100. -/
theorem dirichlet_deriv_128_lt (s : ℂ) (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖deriv (fun z : ℂ => ∑ n ∈ Finset.Icc (1 : ℕ) 127, (n : ℂ) ^ (-z)) s‖ < 110 := by
  have hd := hasDerivAt_dirichlet_sum s (Finset.Icc 1 127) (fun n hn => (Finset.mem_Icc.mp hn).1)
  rw [hd.deriv, Finset.sum_neg_distrib, norm_neg]
  apply lt_of_le_of_lt (norm_sum_le _ _) (lt_of_le_of_lt ?_ log_inv_sqrt_sum_lt)
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hlog := Real.log_nonneg hn1
  have hm := mul_le_mul_of_nonneg_left (norm_cpow_neg_le s hs n (Finset.mem_Icc.mp hn).1) hlog
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog, mul_one_div] using
    hm

/-- For `Re s ≥ 1/2`, the 127-term Dirichlet sum has derivative norm below 90.
Separate logarithm bounds on three index ranges leave a larger remainder budget. -/
theorem dirichlet_deriv_128_lt_90 (s : ℂ) (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖deriv (fun z : ℂ => ∑ n ∈ Finset.Icc (1 : ℕ) 127, (n : ℂ) ^ (-z)) s‖ < 90 := by
  have hd := hasDerivAt_dirichlet_sum s (Finset.Icc 1 127) (fun n hn => (Finset.mem_Icc.mp hn).1)
  rw [hd.deriv, Finset.sum_neg_distrib, norm_neg]
  apply lt_of_le_of_lt (norm_sum_le _ _) (lt_of_le_of_lt ?_ log_inv_sqrt_sum_lt_90)
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hlog := Real.log_nonneg hn1
  have hm := mul_le_mul_of_nonneg_left (norm_cpow_neg_le s hs n (Finset.mem_Icc.mp hn).1) hlog
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog, mul_one_div] using
    hm

/-- For `Re s ≥ 1/2`, the second derivative of the 127-term Dirichlet sum
has norm below 359. Termwise differentiation and the squared-logarithm
sum bound make the estimate independent of the imaginary part. -/
theorem dirichlet_deriv2_128_lt (s : ℂ) (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖iteratedDeriv 2 (fun z : ℂ => ∑ n ∈ Finset.Icc (1 : ℕ) 127, (n : ℂ) ^ (-z)) s‖ < 359 := by
  have heq :
    deriv (fun z : ℂ => ∑ n ∈ Finset.Icc (1 : ℕ) 127, (n : ℂ) ^ (-z)) =
      (fun z : ℂ => ∑ n ∈ Finset.Icc (1 : ℕ) 127, -((Real.log n : ℂ) * (n : ℂ) ^ (-z))) := by
    funext z
    exact
      (hasDerivAt_dirichlet_sum z (Finset.Icc 1 127) (fun n hn => (Finset.mem_Icc.mp hn).1)).deriv
  have hsecond :=
    hasDerivAt_dirichlet_deriv s (Finset.Icc 1 127) (fun n hn => (Finset.mem_Icc.mp hn).1)
  rw [show (2 : ℕ) = 1 + 1 by norm_num only, iteratedDeriv_succ, iteratedDeriv_one, heq,
    hsecond.deriv]
  apply lt_of_le_of_lt (norm_sum_le _ _) (lt_of_le_of_lt ?_ log_sq_inv_sqrt_sum_lt)
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hlog := Real.log_nonneg hn1
  have hm :=
    mul_le_mul_of_nonneg_left (norm_cpow_neg_le s hs n (Finset.mem_Icc.mp hn).1)
      (sq_nonneg (Real.log n))
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog,
    mul_one_div] using hm

/-- Under RH, lower bounds at the 129 horizontal grid points and an error
of at most 38 between the zeta derivative and the 127-term Dirichlet derivative
give `N(100) ≤ 58`. The finite derivative contributes strictly less than 90. -/
theorem count_100_le_58_of_deriv_error (hRH : RiemannHypothesis)
    (hr :
      ∀ t : ℝ,
        t ∈ Set.Icc (1 / 2) (3 / 2) →
          ‖deriv riemannZeta ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I) -
                deriv (fun z : ℂ => ∑ n ∈ Finset.Icc (1 : ℕ) 127, (n : ℂ) ^ (-z))
                  ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)‖ ≤
            38)
    (hg :
      ∀ k : ℕ,
        k ≤ 128 →
          1 ≤ (riemannZeta (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re) :
    zeroCount 100 ≤ 58 := by
  apply count_100_le_58_of_grid_complex hRH
  · intro t ht
    let s : ℂ := (t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I
    have hs : (1 / 2 : ℝ) ≤ s.re := by
      simpa only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using ht.1
    have hfin := dirichlet_deriv_128_lt_90 s hs
    have hrem := hr t ht
    change
      ‖deriv riemannZeta s - deriv (fun z : ℂ => ∑ n ∈ Finset.Icc (1 : ℕ) 127, (n : ℂ) ^ (-z)) s‖ ≤
        38 at hrem
    have htri :=
      norm_add_le
        (deriv riemannZeta s - deriv (fun z : ℂ => ∑ n ∈ Finset.Icc (1 : ℕ) 127, (n : ℂ) ^ (-z)) s)
        (deriv (fun z : ℂ => ∑ n ∈ Finset.Icc (1 : ℕ) 127, (n : ℂ) ^ (-z)) s)
    rw [sub_add_cancel] at htri
    change ‖deriv riemannZeta s‖ ≤ 128
    linarith only [htri, hrem, hfin]
  · exact hg

/-- A bound of 19 for the value error on a circle of radius `1/2` at
height 100 bounds the derivative error at its center by 38. Cauchy's
estimate applies because the circle and its interior avoid the pole. -/
private theorem deriv_error_of_circle (t : ℝ) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hc :
      ∀ z ∈ Metric.sphere ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I) (1 / 2),
        ‖riemannZeta z - f z‖ ≤ 19) :
    ‖deriv riemannZeta ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I) -
          deriv f ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)‖ ≤
      38 := by
  let s : ℂ := (t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I
  have hsi : s.im = 100 := by
    simp only [s, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  have hgood : ∀ z ∈ Metric.closedBall s (1 / 2), z ≠ 1 := by
    intro z hz he
    have hd := Metric.mem_closedBall.mp hz
    rw [Complex.dist_eq] at hd
    have hi := (Complex.abs_im_le_norm (z - s)).trans hd
    rw [he] at hi
    simp only [Complex.sub_im, Complex.one_im, hsi, zero_sub, abs_neg] at hi
    norm_num only at hi
  have hz1 : s ≠ 1 := hgood s (Metric.mem_closedBall_self (by norm_num only))
  have hdiff : DifferentiableOn ℂ (riemannZeta - f) (closure (Metric.ball s (1 / 2))) := by
    intro z hz
    have hne := hgood z (Metric.closure_ball_subset_closedBall hz)
    exact ((differentiableAt_riemannZeta hne).sub (hf z)).differentiableWithinAt
  have hbound :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (show (0 : ℝ) < 1 / 2 by norm_num only)
      hdiff.diffContOnCl hc
  rw [deriv_sub (differentiableAt_riemannZeta hz1) (hf s)] at hbound
  norm_num only at hbound
  exact hbound

/-- A value-error bound of 19 on a circle of radius `1/2` at height 100
gives a second-derivative error of at most 152 at its center. Cauchy's
second-derivative estimate applies because the disc avoids the pole. -/
private theorem deriv2_error_of_circle (t : ℝ) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hc :
      ∀ z ∈ Metric.sphere ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I) (1 / 2),
        ‖riemannZeta z - f z‖ ≤ 19) :
    ‖iteratedDeriv 2 riemannZeta ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I) -
          iteratedDeriv 2 f ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)‖ ≤
      152 := by
  let s : ℂ := (t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I
  have hsi : s.im = 100 := by
    simp only [s, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  have hgood : ∀ z ∈ Metric.closedBall s (1 / 2), z ≠ 1 := by
    intro z hz he
    have hd := Metric.mem_closedBall.mp hz
    rw [Complex.dist_eq] at hd
    have hi := (Complex.abs_im_le_norm (z - s)).trans hd
    rw [he] at hi
    simp only [Complex.sub_im, Complex.one_im, hsi, zero_sub, abs_neg] at hi
    norm_num only at hi
  have hz1 : s ≠ 1 := hgood s (Metric.mem_closedBall_self (by norm_num only))
  have hdiff : DifferentiableOn ℂ (riemannZeta - f) (closure (Metric.ball s (1 / 2))) := by
    intro z hz
    have hne := hgood z (Metric.closure_ball_subset_closedBall hz)
    exact ((differentiableAt_riemannZeta hne).sub (hf z)).differentiableWithinAt
  have hbound :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2
      (show (0 : ℝ) < 1 / 2 by norm_num only) hdiff.diffContOnCl hc
  rw [iteratedDeriv_sub (analyticOn_riemannZeta s hz1).contDiffAt
      (hf.analyticAt s).contDiffAt] at hbound
  norm_num only [Nat.factorial, Nat.cast_ofNat] at hbound
  exact hbound

/-- On the horizontal segment from `1/2 + 100i` to `3/2 + 100i`, the
complex derivative of zeta has norm at most 128. A 127-term Dirichlet
derivative bound and Cauchy's estimate for the explicit remainder supply it. -/
theorem norm_deriv_zeta_100_le (t : ℝ) (ht : t ∈ Set.Icc (1 / 2) (3 / 2)) :
    ‖deriv riemannZeta ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)‖ ≤ 128 := by
  let s : ℂ := (t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I
  let f : ℂ → ℂ := fun z => ∑ n ∈ Finset.Icc (1 : ℕ) 127, (n : ℂ) ^ (-z)
  have hs : (1 / 2 : ℝ) ≤ s.re := by
    simpa only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using ht.1
  have hf : Differentiable ℂ f := by
    intro z
    exact
      (hasDerivAt_dirichlet_sum z (Finset.Icc 1 127)
          (fun n hn => (Finset.mem_Icc.mp hn).1)).differentiableAt
  have hrem := deriv_error_of_circle t f hf (fun z hz => norm_zeta_sub_sum_circle_le t ht z hz)
  change ‖deriv riemannZeta s - deriv f s‖ ≤ 38 at hrem
  have hfin : ‖deriv f s‖ < 90 := dirichlet_deriv_128_lt_90 s hs
  have htri := norm_add_le (deriv riemannZeta s - deriv f s) (deriv f s)
  rw [sub_add_cancel] at htri
  change ‖deriv riemannZeta s‖ ≤ 128
  linarith only [htri, hrem, hfin]

/-- On the horizontal segment at height 100, the second complex derivative
of zeta has norm at most 511. The finite sum contributes less than 359 and
the explicit remainder contributes at most 152 by Cauchy's estimate. -/
theorem norm_deriv2_zeta_100_le (t : ℝ) (ht : t ∈ Set.Icc (1 / 2) (3 / 2)) :
    ‖iteratedDeriv 2 riemannZeta ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)‖ ≤ 511 := by
  let s : ℂ := (t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I
  let f : ℂ → ℂ := fun z => ∑ n ∈ Finset.Icc (1 : ℕ) 127, (n : ℂ) ^ (-z)
  have hs : (1 / 2 : ℝ) ≤ s.re := by
    simpa only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using ht.1
  have hf : Differentiable ℂ f := by
    intro z
    exact
      (hasDerivAt_dirichlet_sum z (Finset.Icc 1 127)
          (fun n hn => (Finset.mem_Icc.mp hn).1)).differentiableAt
  have hrem := deriv2_error_of_circle t f hf (fun z hz => norm_zeta_sub_sum_circle_le t ht z hz)
  change ‖iteratedDeriv 2 riemannZeta s - iteratedDeriv 2 f s‖ ≤ 152 at hrem
  have hfin : ‖iteratedDeriv 2 f s‖ < 359 := dirichlet_deriv2_128_lt s hs
  have htri :=
    norm_add_le (iteratedDeriv 2 riemannZeta s - iteratedDeriv 2 f s) (iteratedDeriv 2 f s)
  rw [sub_add_cancel] at htri
  change ‖iteratedDeriv 2 riemannZeta s‖ ≤ 511
  linarith only [htri, hrem, hfin]

/-- Under RH, the 129 grid lower bounds and a value-error bound of 19 on
radius-`1/2` circles centered on the intervening horizontal segment imply
`N(100) ≤ 58`. Cauchy's estimate supplies the derivative error. -/
theorem count_100_le_58_of_circle_error (hRH : RiemannHypothesis)
    (hc :
      ∀ t : ℝ,
        t ∈ Set.Icc (1 / 2) (3 / 2) →
          ∀ z ∈ Metric.sphere ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I) (1 / 2),
            ‖riemannZeta z - ∑ n ∈ Finset.Icc (1 : ℕ) 127, (n : ℂ) ^ (-z)‖ ≤ 19)
    (hg :
      ∀ k : ℕ,
        k ≤ 128 →
          1 ≤ (riemannZeta (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re) :
    zeroCount 100 ≤ 58 := by
  apply count_100_le_58_of_deriv_error hRH
  · intro t ht
    have hf : Differentiable ℂ (fun z : ℂ => ∑ n ∈ Finset.Icc (1 : ℕ) 127, (n : ℂ) ^ (-z)) := by
      intro z
      exact
        (hasDerivAt_dirichlet_sum z (Finset.Icc 1 127)
            (fun n hn => (Finset.mem_Icc.mp hn).1)).differentiableAt
    exact deriv_error_of_circle t _ hf (hc t ht)
  · exact hg

/-- Under RH, lower bounds of 1 for the real part of zeta at the 129 points
`1/2 + k/128 + 100i` imply `N(100) ≤ 58`. The derivative bound on the segment
follows from the finite Euler–Maclaurin remainder and Cauchy's estimate. -/
theorem count_100_le_58_of_grid_values (hRH : RiemannHypothesis)
    (hg :
      ∀ k : ℕ,
        k ≤ 128 →
          1 ≤ (riemannZeta (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re) :
    zeroCount 100 ≤ 58 := by
  apply count_100_le_58_of_grid_complex hRH
  · exact norm_deriv_zeta_100_le
  · exact hg

/-- Under RH, a lower bound `9/8` for each of the 129 finite
Euler–Maclaurin approximations implies `N(100) ≤ 58`. The analytic error,
grid interpolation, and Cauchy derivative bound are supplied internally. -/
theorem count_100_le_58_of_finite_grid (hRH : RiemannHypothesis)
    (hg :
      ∀ k : ℕ,
        k ≤ 128 →
          let s : ℂ := (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)
          (9 / 8 : ℝ) ≤
            ((∑ n ∈ Finset.Icc (1 : ℕ) 511, (n : ℂ) ^ (-s)) + (512 : ℂ) ^ (1 - s) / (s - 1) +
                (512 : ℂ) ^ (-s) / 2).re) :
    zeroCount 100 ≤ 58 := by
  apply count_100_le_58_of_grid_values hRH
  intro k hk
  let s : ℂ := (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)
  have hcoords : (1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 2 ∧ 99 ≤ s.im ∧ s.im ≤ 101 := by
    dsimp only [s]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hk128 : (k : ℝ) ≤ 128 := by exact_mod_cast hk
    constructor
    · nlinarith only [hk0]
    constructor
    · nlinarith only [hk128]
    constructor <;> norm_num only
  exact zeta_re_lower_of_finite_512 hcoords.1 hcoords.2.1 hcoords.2.2.1 hcoords.2.2.2 (hg k hk)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
