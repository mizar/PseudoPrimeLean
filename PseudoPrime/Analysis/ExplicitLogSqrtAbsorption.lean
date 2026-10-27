/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogSqrtErrorAbsorption
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Explicit cutoffs for logarithmic and square-root remainders

These estimates turn certified analytic error coefficients into explicit decimal
modulus thresholds. They do not supply the analytic error coefficients themselves.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For positive `L`, its logarithm is bounded by its square root. Apply the logarithm
 tangent inequality at `sqrt L / 2` and `log 2 ≤ 1`. This bounds logarithmic remainders
 without an unspecified asymptotic cutoff. -/
theorem log_le_sqrt_of_pos {L : ℝ} (hL : 0 < L) : Real.log L ≤ Real.sqrt L := by
  have hs := Real.sqrt_pos.mpr hL
  have ht := Real.log_le_sub_one_of_pos (div_pos hs (show (0 : ℝ) < 2 by norm_num only))
  rw [Real.log_div hs.ne' (show (2 : ℝ) ≠ 0 by norm_num only)] at ht
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num only)
  have he := Real.log_sqrt hL.le
  nlinarith only [ht, h2, he]

/-- If `B ≥ 0`, `δ > 0`, and positive `L` exceeds the two displayed bounds,
 `A + B log L + C sqrt L ≤ δ L / 2`. Bound the logarithm by the square root and
 allocate `δ L / 4` to each error group. The real coefficients need no integrality
 assumptions; applications can supply exact rational coefficients. -/
theorem log_sqrt_error_le_half {A B C δ L : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hL : 0 < L)
    (hA : 4 * A / δ ≤ L) (hBC : (4 * (B + C) / δ) ^ 2 ≤ L) :
    A + B * Real.log L + C * Real.sqrt L ≤ δ * L / 2 := by
  have ha := (div_le_iff₀ hδ).mp hA
  have hs : 4 * (B + C) / δ ≤ Real.sqrt L := Real.le_sqrt_of_sq_le hBC
  have hs' := (div_le_iff₀ hδ).mp hs
  have hm := mul_le_mul_of_nonneg_right hs' (Real.sqrt_nonneg L)
  have hl := mul_le_mul_of_nonneg_left (log_le_sqrt_of_pos hL) hB
  rw [mul_right_comm (Real.sqrt L) δ, ← pow_two, Real.sq_sqrt hL.le] at hm
  linarith only [ha, hm, hl]

/-- Explicit logarithmic cutoff for the remainder `A + B log L + C sqrt L`.
 The maximum retains the caller's analytic starting value `base`, enforces `L ≥ 1`,
 and reserves one quarter of `δ L` for each error group. It is used to certify
 decimal modulus thresholds after the analytic coefficients have been proved. -/
noncomputable def logSqrtErrorThreshold (A B C δ base : ℝ) : ℝ :=
  max (max 1 base) (max (4 * A / δ) ((4 * (B + C) / δ) ^ 2))

/-- Above `logSqrtErrorThreshold`, a nonnegative logarithmic coefficient `B` and
 positive allowance `δ` give an error of at most `δ L / 2`. Extract the positive
 scale and both explicit bounds from the maximum, then apply error absorption. -/
theorem log_sqrt_error_le_half_of_threshold {A B C δ base L : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hL : logSqrtErrorThreshold A B C δ base ≤ L) :
    A + B * Real.log L + C * Real.sqrt L ≤ δ * L / 2 := by
  have hlow := (max_le_iff.mp hL).1
  have hhigh := (max_le_iff.mp hL).2
  have hpos : 0 < L := lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num only) (max_le_iff.mp hlow).1
  exact log_sqrt_error_le_half hB hδ hpos (max_le_iff.mp hhigh).1 (max_le_iff.mp hhigh).2

/-- The natural logarithm of ten is at least two. Compare ten with nine and use
 the certified lower bound for `log 3`. This converts decimal powers to log scales. -/
theorem two_le_log_ten : (2 : ℝ) ≤ Real.log 10 := by
  have hm :=
    Real.log_le_log (show (0 : ℝ) < 9 by norm_num only) (show (9 : ℝ) ≤ 10 by norm_num only)
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num only, Real.log_pow] at hm
  norm_num only at hm
  linarith only [hm, Real.log_three_gt_d9]

/-- A natural modulus `q ≥ 10^d` has `log q ≥ 2d`. Cast the power comparison,
 apply monotonicity of the logarithm, and use `2 ≤ log 10`. This avoids evaluating
 the potentially enormous integer power inside the analytic proof. -/
theorem log_nat_ge_of_decimal {q d : ℕ} (hq : 10 ^ d ≤ q) : 2 * (d : ℝ) ≤ Real.log q := by
  have hp : (0 : ℝ) < (10 : ℝ) ^ d := pow_pos (by norm_num only) d
  have hcast : (10 : ℝ) ^ d ≤ (q : ℝ) := by exact_mod_cast hq
  have hm := Real.log_le_log hp hcast
  rw [Real.log_pow] at hm
  have hl := mul_le_mul_of_nonneg_left two_le_log_ten (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  linarith only [hm, hl]

/-- A decimal exponent whose doubled value dominates the explicit cutoff gives
 error absorption for every natural modulus at least `10^d`. The conclusion is
 conditional on the supplied coefficients, not on any unproved analytic estimate.
 Compose the decimal logarithm lower bound with the cutoff theorem. -/
theorem log_log_sqrt_error_le_half_of_decimal_bound {A B C δ base : ℝ} {q d : ℕ} (hB : 0 ≤ B)
    (hδ : 0 < δ) (hd : logSqrtErrorThreshold A B C δ base ≤ 2 * (d : ℝ)) (hq : 10 ^ d ≤ q) :
    A + B * Real.log (Real.log q) + C * Real.sqrt (Real.log q) ≤ δ * Real.log q / 2 := by
  exact log_sqrt_error_le_half_of_threshold hB hδ (hd.trans (log_nat_ge_of_decimal hq))

/-- A squared coefficient gap implies a strict square-root gap for nonnegative D,a.
Square D sqrt a and compare squares. This turns rational certificates into main-term margins. -/
theorem coefficient_lt_mul_sqrt_of_sq_lt {D a M δ : ℝ} (hD : 0 ≤ D) (ha : 0 ≤ a)
    (hgap : (M + δ) ^ 2 < D ^ 2 * a) : M + δ < D * Real.sqrt a := by
  have hs : 0 ≤ D * Real.sqrt a := mul_nonneg hD (Real.sqrt_nonneg a)
  have he : (D * Real.sqrt a) ^ 2 = D ^ 2 * a := by rw [mul_pow, Real.sq_sqrt ha]
  nlinarith only [hgap, he, hs]

/-- A squared main-term gap and error at most δ L / 2 imply a strict comparison
at scale a L², for positive δ,L and nonnegative D,a. Multiply the coefficient gap by L
and expand the square root. This forces a witness once the analytic bounds are supplied. -/
theorem main_term_lt_of_sq_gap_and_error {D a M δ L E : ℝ} (hD : 0 ≤ D) (ha : 0 ≤ a) (hL : 0 < L)
    (hδ : 0 < δ) (hgap : (M + δ) ^ 2 < D ^ 2 * a) (hE : E ≤ δ * L / 2) :
    M * L + E < D * Real.sqrt (a * L ^ 2) := by
  have hc := mul_lt_mul_of_pos_right (coefficient_lt_mul_sqrt_of_sq_lt hD ha hgap) hL
  have hp := mul_pos hδ hL
  rw [Real.sqrt_mul ha, Real.sqrt_sq hL.le]
  nlinarith only [hc, hE, hp]

/-- Decimal exponent obtained by rounding half the explicit logarithmic cutoff up.
The associated natural threshold is 10^d. This real-valued specification is noncomputable;
exact rational certificates may supply a smaller concrete exponent. -/
noncomputable def logSqrtErrorDecimalExponent (A B C δ base : ℝ) : ℕ :=
  Nat.ceil (logSqrtErrorThreshold A B C δ base / 2)

/-- Twice the rounded decimal exponent dominates the logarithmic cutoff.
Apply the upper bound of the natural ceiling and clear the factor two.
This supplies the integer rounding obligation for explicit modulus thresholds. -/
theorem threshold_le_twice_decimalExponent (A B C δ base : ℝ) :
    logSqrtErrorThreshold A B C δ base ≤ 2 * (logSqrtErrorDecimalExponent A B C δ base : ℝ) := by
  have h :
    logSqrtErrorThreshold A B C δ base / 2 ≤ (logSqrtErrorDecimalExponent A B C δ base : ℝ) :=
    Nat.le_ceil _
  linarith only [h]

/-- Above the rounded decimal threshold, the logarithmic remainder is absorbed
into half the positive allowance. Compose the ceiling bound with decimal-to-logarithm
conversion; the analytic coefficients remain explicit inputs. -/
theorem log_log_sqrt_error_le_half_of_decimalExponent {A B C δ base : ℝ} {q : ℕ} (hB : 0 ≤ B)
    (hδ : 0 < δ) (hq : 10 ^ logSqrtErrorDecimalExponent A B C δ base ≤ q) :
    A + B * Real.log (Real.log q) + C * Real.sqrt (Real.log q) ≤ δ * Real.log q / 2 := by
  exact
    log_log_sqrt_error_le_half_of_decimal_bound hB hδ
      (threshold_le_twice_decimalExponent A B C δ base) hq

/-- A certified decimal cutoff and squared coefficient gap give a strict main-term
comparison for every larger modulus. Combine error absorption with square-root
scaling. Analytic estimates for the supplied coefficients are separate obligations. -/
theorem main_term_lt_of_decimal_bound {A B C D a M δ base : ℝ} {q d : ℕ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hD : 0 ≤ D) (ha : 0 ≤ a) (hgap : (M + δ) ^ 2 < D ^ 2 * a)
    (hd : logSqrtErrorThreshold A B C δ base ≤ 2 * (d : ℝ)) (hq : 10 ^ d ≤ q) :
    M * Real.log q + (A + B * Real.log (Real.log q) + C * Real.sqrt (Real.log q)) <
      D * Real.sqrt (a * (Real.log q) ^ 2) := by
  have hscale := hd.trans (log_nat_ge_of_decimal hq)
  have hone : (1 : ℝ) ≤ Real.log q := (le_max_left 1 base).trans ((le_max_left _ _).trans hscale)
  exact
    main_term_lt_of_sq_gap_and_error hD ha (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hone) hδ
      hgap (log_log_sqrt_error_le_half_of_decimal_bound hB hδ hd hq)

/-- A positive natural input n≤10^d has log(n)≤(5/2)d.
Use logarithmic monotonicity and the certified upper bound log(10)≤5/2.
This bounds an entire smaller-input range without enumerating its elements. -/
theorem log_nat_le_of_decimal_upper {n d : ℕ} (hn : 0 < n) (hbound : n ≤ 10 ^ d) :
    Real.log n ≤ (5 / 2 : ℝ) * d := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hb : (n : ℝ) ≤ (10 : ℝ) ^ d := by exact_mod_cast hbound
  have hl := Real.log_le_log hn0 hb
  rw [Real.log_pow] at hl
  have h10 : Real.log (10 : ℝ) ≤ 5 / 2 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num only, Real.log_mul (by norm_num only) (by norm_num only)]
    linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hm := mul_le_mul_of_nonneg_left h10 (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  linarith only [hl, hm]

end PseudoPrime.Analysis
