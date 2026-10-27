/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialRampLocalCorrection

/-! # Signed prime-power local series for the exponential ramp

Geometric domination justifies finite prefix and tail separation.
Parity counting retains only one endpoint loss for a negative local value.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a quadratic local value, Re(1+c^k) is at most two at every power.
Split the possible values and parity to bound the signed local series absolutely. -/
theorem quadratic_one_add_pow_re_le_two {c : ℂ} (hc : c = 0 ∨ c = 1 ∨ c = -1) (k : ℕ) :
    (1 + c ^ k).re ≤ 2 := by
  rcases hc with rfl | rfl | rfl
  · by_cases hk : k = 0
    · norm_num only [hk, pow_zero, Complex.add_re, Complex.one_re, Complex.re_ofNat]
    · norm_num only [zero_pow hk, add_zero, Complex.one_re, Complex.re_ofNat]
  · norm_num only [one_pow, Complex.add_re, Complex.one_re, Complex.re_ofNat]
  · rcases Nat.even_or_odd k with hk | hk
    · norm_num only [hk.neg_one_pow, Complex.add_re, Complex.one_re, Complex.re_ofNat]
    · norm_num only [hk.neg_one_pow, add_neg_cancel, Complex.zero_re]

/-- The signed local term has norm at most 2exp(-u) for a quadratic local value.
Use the two-sided coefficient and ramp bounds to justify absolute convergence. -/
theorem norm_exponentialRampLocalCorrection_le_exp {c : ℂ} (hc : c = 0 ∨ c = 1 ∨ c = -1) (u : ℝ)
    (k : ℕ) : ‖exponentialRampLocalCorrection c u k‖ ≤ 2 * Real.exp (-u) := by
  have h0 := quadratic_one_add_pow_re_nonneg hc k
  have h2 := quadratic_one_add_pow_re_le_two hc k
  have hm0 := mul_nonneg h0 (Real.exp_pos (-u)).le
  have hm2 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-u)).le
  have hW := exponentialRampWeight_bounds u
  rw [Real.norm_eq_abs, abs_le]
  dsimp only [exponentialRampLocalCorrection]
  constructor
  · linarith only [hm2, hW.1]
  · linarith only [hm0, hW.2]

/-- The exponential at height (k+1)/x is a geometric power of exp(-1/x).
The exponential multiple formula identifies a summable majorant at positive scale. -/
theorem exp_neg_div_nat_eq_power (x : ℝ) (k : ℕ) :
    Real.exp (-((k + 1 : ℕ) : ℝ) / x) = Real.exp (-1 / x) ^ (k + 1) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- For positive scale, quadratic local value and heights growing at least linearly,
the signed local series is summable. Dominate its norm by a geometric exponential.
This justifies separating its finite prefix and nonpositive tail. -/
theorem summable_exponentialRampLocalCorrection {c : ℂ} (hc : c = 0 ∨ c = 1 ∨ c = -1) {x : ℝ}
    (hx : 0 < x) (u : ℕ → ℝ) (hu : ∀ k, ((k + 1 : ℕ) : ℝ) / x ≤ u k) :
    Summable (fun k ↦ exponentialRampLocalCorrection c (u k) (k + 1)) := by
  have hr : ‖Real.exp (-1 / x)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by norm_num only) hx
  have hs := (summable_geometric_of_norm_lt_one hr).mul_right (Real.exp (-1 / x))
  have hmajor : Summable (fun k : ℕ ↦ 2 * Real.exp (-1 / x) ^ (k + 1)) := by
    simpa only [pow_succ] using hs.mul_left 2
  apply hmajor.of_norm_bounded
  intro k
  have he : Real.exp (-(u k)) ≤ Real.exp (-((k + 1 : ℕ) : ℝ) / x) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    exact neg_le_neg (hu k)
  calc
    _ ≤ 2 * Real.exp (-(u k)) := norm_exponentialRampLocalCorrection_le_exp hc _ _
    _ ≤ 2 * Real.exp (-((k + 1 : ℕ) : ℝ) / x) := mul_le_mul_of_nonneg_left he (by norm_num only)
    _ = _ := by rw [exp_neg_div_nat_eq_power]

/-- A summable quadratic local series is at most its first m terms when all later
heights reach the cutoff 99/40. The exact prefix-tail identity retains the nonpositive tail. -/
theorem exponentialRampLocalCorrection_tsum_le_prefix {c : ℂ} (hc : c = 0 ∨ c = 1 ∨ c = -1) {x : ℝ}
    (hx : 0 < x) (u : ℕ → ℝ) (hu : ∀ k, ((k + 1 : ℕ) : ℝ) / x ≤ u k) (m : ℕ)
    (htail : ∀ k, 99 / 40 ≤ u (k + m)) :
    (∑' k : ℕ, exponentialRampLocalCorrection c (u k) (k + 1)) ≤
      ∑ k ∈ Finset.range m, exponentialRampLocalCorrection c (u k) (k + 1) := by
  have hs := summable_exponentialRampLocalCorrection hc hx u hu
  have he := hs.sum_add_tsum_nat_add m
  have ht : (∑' k : ℕ, exponentialRampLocalCorrection c (u (k + m)) (k + m + 1)) ≤ 0 :=
    tsum_nonpos (fun k ↦ exponentialRampLocalCorrection_tail_nonpos hc (htail k) _)
  linarith only [he, ht]

/-- For integer base p>1 and positive x, p^(k+1)/x is at least (k+1)/x.
Exponential power growth supplies the summable majorant for prime-power local terms. -/
theorem prime_power_div_scale_ge_linear {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 0 < x) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) / x ≤ (p : ℝ) ^ (k + 1) / x := by
  have hn : k + 1 ≤ p ^ (k + 1) := (Nat.lt_pow_self hp).le
  have hr : ((k + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ (k + 1) := by exact_mod_cast hn
  exact div_le_div_of_nonneg_right hr hx.le

/-- For p>1 and X>0, the power just after floor(log(X)/log(p)) exceeds X.
Multiply the strict floor bound by log(p) and compare positive logarithms. -/
theorem prime_power_above_log_floor {p : ℕ} (hp : 1 < p) {X : ℝ} (hX : 0 < X) :
    X < (p : ℝ) ^ (⌊Real.log X / Real.log p⌋₊ + 1) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hlp := Real.log_pos hpR
  have h := (div_lt_iff₀ hlp).mp (Nat.lt_floor_add_one (Real.log X / Real.log p))
  apply (Real.log_lt_log_iff hX (pow_pos (zero_lt_one.trans hpR) _)).mp
  rw [Real.log_pow, Nat.cast_add, Nat.cast_one]
  exact h

/-- For positive x and p>1, powers beyond the logarithmic cutoff have height at least 99/40.
Monotonicity of powers and the strict floor endpoint permit dropping the signed tail. -/
theorem prime_power_tail_above_cutoff {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 0 < x) {k : ℕ}
    (hk : ⌊Real.log ((99 / 40 : ℝ) * x) / Real.log p⌋₊ ≤ k) : 99 / 40 ≤ (p : ℝ) ^ (k + 1) / x := by
  have hcut := prime_power_above_log_floor hp (mul_pos (by norm_num only : (0 : ℝ) < 99 / 40) hx)
  have hpow : (p : ℝ) ^ (⌊Real.log ((99 / 40 : ℝ) * x) / Real.log p⌋₊ + 1) ≤ (p : ℝ) ^ (k + 1) := by
    exact_mod_cast Nat.pow_le_pow_right (zero_lt_one.trans hp) (Nat.succ_le_succ hk)
  apply (le_div_iff₀ hx).mpr
  exact (hcut.trans_le hpow).le

/-- For quadratic local value, p>1 and positive x, the actual signed prime-power
series is at most the logarithmic cutoff count plus one for local value minus one.
Prove convergence, drop the nonpositive tail and apply exact odd-power counting. -/
theorem exponentialRamp_prime_power_correction_le_count {c : ℂ} (hc : c = 0 ∨ c = 1 ∨ c = -1)
    {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 0 < x) :
    (∑' k : ℕ, exponentialRampLocalCorrection c ((p : ℝ) ^ (k + 1) / x) (k + 1)) ≤
      (⌊Real.log ((99 / 40 : ℝ) * x) / Real.log p⌋₊ : ℝ) + if c = -1 then 1 else 0 := by
  let m := ⌊Real.log ((99 / 40 : ℝ) * x) / Real.log p⌋₊
  let u := fun k : ℕ ↦ (p : ℝ) ^ (k + 1) / x
  have hu : ∀ k, ((k + 1 : ℕ) : ℝ) / x ≤ u k := prime_power_div_scale_ge_linear hp hx
  have ht : ∀ k, 99 / 40 ≤ u (k + m) := fun k ↦
    prime_power_tail_above_cutoff hp hx (Nat.le_add_left m k)
  have hu0 : ∀ k, 0 ≤ u k := fun k ↦ div_nonneg (pow_nonneg (Nat.cast_nonneg p) _) hx.le
  exact
    (exponentialRampLocalCorrection_tsum_le_prefix hc hx u hu m ht).trans
      (exponentialRampLocalCorrection_sum_le hc u hu0 m)

/-- For p>1 and X≥1, the retained power count times log(p) is at most log(X).
Use the natural floor bound to replace the per-prime count by the cutoff logarithm. -/
theorem prime_power_log_count_le_cutoff_log {p : ℕ} (hp : 1 < p) {X : ℝ} (hX : 1 ≤ X) :
    (⌊Real.log X / Real.log p⌋₊ : ℝ) * Real.log p ≤ Real.log X := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hlp := Real.log_pos hpR
  have hf := Nat.floor_le (div_nonneg (Real.log_nonneg hX) hlp.le)
  exact (le_div_iff₀ hlp).mp hf

/-- For p>1, positive scale and cutoff X=(99/40)x≥1, the actual log-weighted
signed local series is at most log(X) plus log(p) only for local value minus one.
This is the sharp per-prime input to the conductor-quotient correction. -/
theorem exponentialRamp_prime_power_log_correction_le {c : ℂ} (hc : c = 0 ∨ c = 1 ∨ c = -1) {p : ℕ}
    (hp : 1 < p) {x : ℝ} (hx : 0 < x) (hcut : 1 ≤ (99 / 40 : ℝ) * x) :
    Real.log p * (∑' k : ℕ, exponentialRampLocalCorrection c ((p : ℝ) ^ (k + 1) / x) (k + 1)) ≤
      Real.log ((99 / 40 : ℝ) * x) + if c = -1 then Real.log p else 0 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hsum :=
    mul_le_mul_of_nonneg_left (exponentialRamp_prime_power_correction_le_count hc hp hx)
      (Real.log_pos hpR).le
  have hcount := prime_power_log_count_le_cutoff_log hp hcut
  by_cases hcneg : c = -1
  · simp only [ite_eq_left hcneg] at hsum ⊢
    nlinarith only [hsum, hcount]
  · simp only [ite_eq_right hcneg, add_zero] at hsum ⊢
    nlinarith only [hsum, hcount]

end PseudoPrime.Analysis
