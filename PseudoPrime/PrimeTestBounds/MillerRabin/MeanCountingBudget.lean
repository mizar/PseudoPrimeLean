/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanCofactorCells
public import PseudoPrime.Combinatorics.LogFactorialBounds

/-! # Explicit counting budgets for selected prime products

Convert a logarithmic binomial budget to the strict count needed by the average-logarithm
Miller–Rabin criterion, retaining the finite Stirling error.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `b ≥ 2002` and `x ≥ b - 2`, the displayed logarithmic estimate holds.
Apply the tangent bound for `log (b / (b - 2))` and bound the rational error.
This controls the rounding loss in the binomial base. -/
theorem mean_log_base {b x : ℝ} (hb : 2002 ≤ b) (hx : b - 2 ≤ x) :
    Real.log b + (999 / 1000 : ℝ) ≤ Real.log x + 1 := by
  have hb0 : 0 < b := by linarith only [hb]
  have hd : 0 < b - 2 := by linarith only [hb]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hb0 hd)
  rw [Real.log_div hb0.ne' hd.ne', div_sub_one hd.ne'] at hlog
  have he : b - (b - 2) = 2 := by ring
  rw [he] at hlog
  have hc : (2 : ℝ) / (b - 2) ≤ 1 / 1000 := by
    apply (div_le_iff₀ hd).mpr
    linarith only [hb]
  have hl := Real.log_le_log hd hx
  linarith only [hlog, hc, hl]

/-- Suppose `b ≥ 0`, `1 ≤ k ≤ M`, `τ ≤ b + 1`, `δ ≥ 0`, and `b ^ 2 ≤ P`.
The stated mean budget then bounds the descending-factorial base below by `b - 2`.
Clear the positive denominators and compare `b ^ 2` with `(b + 1) * (b - 1)`.
This allows the mean constraint to feed the binomial logarithm estimate. -/
theorem mean_choose_base {M k : ℕ} {b τ δ P : ℝ} (hb : 0 ≤ b) (hk : 0 < k) (hkM : k ≤ M)
    (hτ : τ ≤ b + 1) (hδ : 0 ≤ δ) (hP : b ^ 2 ≤ P) (hmean : (k : ℝ) * P ≤ (τ - δ) * M) :
    b - 2 ≤ ((M + 1 - k : ℕ) : ℝ) / k := by
  have hk0 : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hp := mul_le_mul_of_nonneg_left hP hk0.le
  have ht := mul_le_mul_of_nonneg_right hτ hM0
  have hd := mul_nonneg hδ hM0
  have hm : (k : ℝ) * b ^ 2 ≤ (b + 1) * M := by nlinarith only [hp, hmean, ht, hd]
  have hh : (b + 1) * ((k : ℝ) * (b - 1)) ≤ (b + 1) * M := by nlinarith only [hm, hk0]
  have hr : (k : ℝ) * (b - 1) ≤ M :=
    (mul_le_mul_iff_right₀ (show 0 < b + 1 by linarith only [hb])).mp hh
  have he : ((M + 1 - k : ℕ) : ℝ) = (M : ℝ) + 1 - k := by
    rw [Nat.cast_sub (hkM.trans (Nat.le_succ M)), Nat.cast_succ]
  apply (le_div_iff₀ hk0).mpr
  rw [he]
  nlinarith only [hr, hk0]

/-- With `b ≥ 2002`, the mean budget and `τ ≤ b + 1` imply the logarithmic
binomial-base condition used by `mean_count_of_log_budget`. Combine the base estimate
with the logarithmic rounding bound. This avoids a separate large-product calculation. -/
theorem mean_log_choose_base {M k : ℕ} {b τ δ P : ℝ} (hb : 2002 ≤ b) (hk : 0 < k) (hkM : k ≤ M)
    (hτ : τ ≤ b + 1) (hδ : 0 ≤ δ) (hP : b ^ 2 ≤ P) (hmean : (k : ℝ) * P ≤ (τ - δ) * M) :
    Real.log b + (999 / 1000 : ℝ) ≤ Real.log (((M + 1 - k : ℕ) : ℝ) / k) + 1 := by
  exact mean_log_base hb (mean_choose_base (by linarith only [hb]) hk hkM hτ hδ hP hmean)

/-- For positive `u ≤ U` and nonnegative coefficients, a certified gap at `U` gives
the displayed strict gap at `u` whenever `g * L > 120`. The two inverse powers decrease
with their positive argument. This lets one rational endpoint certify an entire scale cell. -/
theorem mean_gap_of_endpoint {α P a d u U g L : ℝ} (hα : 0 ≤ α) (hP : 0 < P) (ha : 0 ≤ a)
    (hd : 0 ≤ d) (hu : 0 < u) (huU : u ≤ U) (hL : 0 ≤ L)
    (hcert :
      (1 - α) + g ≤ (α / P) * (a / 2 + ((999 / 1000) * a + d / 2) / U + ((999 / 1000) * d) / U ^ 2))
    (hsize : 120 < g * L) :
    (1 - α) * L + 120 <
      (α / P) * (a / 2 + ((999 / 1000) * a + d / 2) / u + ((999 / 1000) * d) / u ^ 2) * L := by
  have hc : 0 ≤ (999 / 1000 : ℝ) * a + d / 2 := by linarith only [ha, hd]
  have hd' : 0 ≤ (999 / 1000 : ℝ) * d := mul_nonneg (by norm_num only) hd
  have hs := pow_le_pow_left₀ hu.le huU 2
  have h1 := div_le_div_of_nonneg_left hc hu huU
  have h2 := div_le_div_of_nonneg_left hd' (pow_pos hu 2) hs
  have hh :
    a / 2 + ((999 / 1000) * a + d / 2) / U + ((999 / 1000) * d) / U ^ 2 ≤
      a / 2 + ((999 / 1000) * a + d / 2) / u + ((999 / 1000) * d) / u ^ 2 := by
    linarith only [h1, h2]
  have hm := mul_le_mul_of_nonneg_left hh (div_nonneg hα hP.le)
  have hmon := mul_le_mul_of_nonneg_right hm hL
  have hc' := mul_le_mul_of_nonneg_right hcert hL
  nlinarith only [hmon, hc', hsize]

/-- For positive `u`, a lower bound for the selected size `k`, the displayed scalar gap,
a cofactor logarithm bound, and a loss budget of 120 imply the strict logarithmic counting
budget. Expand the main term using `u ≠ 0` and multiply the floor bound by a nonnegative
factor. This connects endpoint certificates to `mean_count_of_log_budget`. -/
theorem mean_log_budget_of_gap {L α P a d u : ℝ} {k m : ℕ} {τ δ : ℝ} (hu : 0 < u)
    (hk : (α / P) * L * (a / u + d / u ^ 2) - 2 ≤ k)
    (hgap :
      (1 - α) * L + 120 <
        (α / P) * (a / 2 + ((999 / 1000) * a + d / 2) / u + ((999 / 1000) * d) / u ^ 2) * L)
    (hlogm : Real.log m < (1 - α) * L)
    (hloss :
      Real.log τ - Real.log δ + Real.log k / 2 + Real.log (2 * Real.pi) / 2 + 1 / (12 * (k : ℝ)) +
          2 * (u / 2 + 999 / 1000) ≤
        120) :
    Real.log τ + Real.log m <
      Real.log δ +
        ((k : ℝ) * (u / 2 + 999 / 1000) - Real.log k / 2 - Real.log (2 * Real.pi) / 2 -
          1 / (12 * (k : ℝ))) := by
  have hbase : 0 ≤ u / 2 + (999 / 1000 : ℝ) := by linarith only [hu]
  have hmul := mul_le_mul_of_nonneg_right hk hbase
  have h1 : (a / u) * u = a := div_mul_cancel₀ _ hu.ne'
  have h2 : (d / u ^ 2) * u = d / u := by rw [pow_two, div_mul_eq_div_div, div_mul_cancel₀ _ hu.ne']
  have h3 : ((999 / 1000 : ℝ) * a + d / 2) / u = (999 / 1000) * (a / u) + (d / u) / 2 := by ring
  have h4 : ((999 / 1000 : ℝ) * d) / u ^ 2 = (999 / 1000) * (d / u ^ 2) := by ring
  have he :
    (a / u + d / u ^ 2) * (u / 2 + 999 / 1000) =
      a / 2 + ((999 / 1000) * a + d / 2) / u + ((999 / 1000) * d) / u ^ 2 := by
    rw [h3, h4]
    nlinarith only [h1, h2]
  have he' := congrArg (fun z : ℝ ↦ (α / P) * L * z) he
  nlinarith only [hmul, hgap, hlogm, hloss, he']

/-- For positive `τ`, `δ`, `m`, and `1 ≤ k ≤ M`, the displayed lower bound for the
binomial base and strict logarithmic budget imply `τ * m < δ * choose M k`.
Use the finite-error Stirling estimate and the strict monotonicity of the logarithm.
This is the scalar count input for the selected-product witness criteria. -/
theorem mean_count_of_log_budget {M k m : ℕ} {τ δ u : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (hm : 0 < m)
    (hk0 : k ≠ 0) (hk : k ≤ M)
    (hbase : u / 2 + (999 / 1000 : ℝ) ≤ Real.log (((M + 1 - k : ℕ) : ℝ) / k) + 1)
    (hbudget :
      Real.log τ + Real.log m <
        Real.log δ +
          ((k : ℝ) * (u / 2 + 999 / 1000) - Real.log k / 2 - Real.log (2 * Real.pi) / 2 -
            1 / (12 * (k : ℝ)))) :
    τ * m < δ * Nat.choose M k := by
  have hchoose := Combinatorics.log_choose_stirling_lower hk0 hk
  have hm' := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hl : Real.log τ + Real.log m < Real.log δ + Real.log (Nat.choose M k : ℝ) := by
    nlinarith only [hchoose, hm', hbudget]
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hc0 : (0 : ℝ) < Nat.choose M k := Nat.cast_pos.mpr (Nat.choose_pos hk)
  apply (Real.log_lt_log_iff (mul_pos hτ hm0) (mul_pos hδ hc0)).mp
  rw [Real.log_mul hτ.ne' hm0.ne', Real.log_mul hδ.ne' hc0.ne']
  exact hl

/-- For a large prime cofactor of an odd `n > 1`, the stated theta estimates,
mean bound, binomial-base bound and strict logarithmic budget give a rejecting prime up to
`B`. Convert the logarithmic budget to a strict count and apply the theta criterion.
This connects the finite Stirling error to witness extraction. -/
theorem large_cofactor_of_log_budget {n m q : ℕ} (hn : 1 < n) (ho : Odd n) (hm : 1 < m)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = m * q) (B M k : ℕ) (τ δ P a η : ℝ) (hB : 32 ≤ B)
    (hk : 1 ≤ k) (hkM : k ≤ M) (hM0 : 1 ≤ M) (hτ : 0 < τ) (hδ : 0 < δ) (hmargin : 0 ≤ τ - δ)
    (hsize : τ ≤ Real.log q) (hθB : a * B ≤ Chebyshev.theta B)
    (hθ : ∀ t ∈ Set.Icc ((B : ℝ) / 16) B, η * t ≤ Chebyshev.theta t)
    (hupper : Chebyshev.theta B ≤ P)
    (hM : (M : ℝ) ≤ (B : ℝ) * (a / Real.log B + (15 * η / 16) / Real.log B ^ 2))
    (hmean : (k : ℝ) * P ≤ (τ - δ) * M)
    (hbase : Real.log B / 2 + (999 / 1000 : ℝ) ≤ Real.log (((M + 1 - k : ℕ) : ℝ) / k) + 1)
    (hbudget :
      Real.log τ + Real.log m <
        Real.log δ +
          ((k : ℝ) * (Real.log B / 2 + 999 / 1000) - Real.log k / 2 - Real.log (2 * Real.pi) / 2 -
            1 / (12 * (k : ℝ)))) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hc :=
    mean_count_of_log_budget hτ hδ (Nat.zero_lt_of_lt hm) (Nat.ne_zero_of_lt (Nat.zero_lt_of_lt hk))
      hkM hbase hbudget
  exact
    large_cofactor_of_theta hn ho hm hq hq2 hprod B M k τ δ P a η hB hk hM0 hτ.le hδ.le hmargin
      hsize hθB hθ hupper hM hmean hc

end PseudoPrime.PrimeTestBounds.MillerRabin
