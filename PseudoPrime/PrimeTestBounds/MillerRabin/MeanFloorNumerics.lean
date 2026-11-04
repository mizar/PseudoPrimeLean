/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanScalarCells
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Floor and logarithmic budgets for mean prime-product counting

Coarse inequalities below certify the floor and loss budgets without expanding a prime
table or a large factorial.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If `99 / 100 ≤ a ≤ 1`, `0 ≤ d ≤ 1`, and `20 ≤ u ≤ 48`, the prime-supply
factor `a / u + d / u ^ 2` lies between `1 / 100` and `21 / 400`.
Compare positive denominators at the interval endpoints. These bounds absorb floor losses. -/
theorem mean_supply_factor_bounds {a d u : ℝ} (ha : (99 / 100 : ℝ) ≤ a) (ha1 : a ≤ 1) (hd : 0 ≤ d)
    (hd1 : d ≤ 1) (hu : 20 ≤ u) (huU : u ≤ 48) :
    (1 / 100 : ℝ) ≤ a / u + d / u ^ 2 ∧ a / u + d / u ^ 2 ≤ 21 / 400 := by
  have hu0 : 0 < u := by linarith only [hu]
  have hu2 : (400 : ℝ) ≤ u ^ 2 := by nlinarith only [hu]
  have hlower : (99 / 100 : ℝ) / 48 ≤ a / u := div_le_div₀ (by linarith only [ha]) ha hu0 huU
  have hterm0 : 0 ≤ d / u ^ 2 := div_nonneg hd (sq_nonneg _)
  have hupper : a / u ≤ (1 : ℝ) / 20 := div_le_div₀ (by norm_num only) ha1 (by norm_num only) hu
  have hupper2 : d / u ^ 2 ≤ (1 : ℝ) / 400 :=
    div_le_div₀ (by norm_num only) hd1 (by norm_num only) hu2
  constructor <;> linarith only [hlower, hterm0, hupper, hupper2]

/-- If `b ≥ 52000`, `50000 ≤ τ ≤ b + 1`, `1 ≤ P ≤ 2`, and the supply factor
lies in `[1 / 100, 21 / 400]`, all three displayed floor-size budgets hold.
Bound the floored supply below by `b ^ 2 / 200` and compare the remaining polynomial
terms. This removes floor-size assumptions from the large-cofactor argument. -/
theorem mean_floor_size_budgets {b τ P f : ℝ} (hb : 52000 ≤ b) (hτ : 50000 ≤ τ) (htau : τ ≤ b + 1)
    (hP : 1 ≤ P) (hP2 : P ≤ 2) (hf : (1 / 100 : ℝ) ≤ f) (hf2 : f ≤ 21 / 400) :
    τ - 4 ≤ P * b ^ 2 ∧
      P * b ^ 2 ≤ (τ - 4) * (⌊b ^ 2 * f⌋₊ : ℝ) ∧ 4 * b ^ 2 * f + (τ - 4) ≤ P * b ^ 2 := by
  have hB : (200 : ℝ) ≤ b ^ 2 := by nlinarith only [hb]
  have hB0 : 0 ≤ b ^ 2 := sq_nonneg b
  have hfloor := Nat.lt_floor_add_one (b ^ 2 * f)
  have hflo := mul_le_mul_of_nonneg_left hf hB0
  have hfhi := mul_le_mul_of_nonneg_left hf2 hB0
  have hp := mul_le_mul_of_nonneg_right hP hB0
  have hp2 := mul_le_mul_of_nonneg_right hP2 hB0
  have hM : b ^ 2 / 200 ≤ (⌊b ^ 2 * f⌋₊ : ℝ) := by linarith only [hfloor, hflo, hB]
  have hD : 0 ≤ (τ - 50000) * ((⌊b ^ 2 * f⌋₊ : ℝ) - b ^ 2 / 200) :=
    mul_nonneg (by linarith only [hτ]) (by linarith only [hM])
  constructor
  · nlinarith only [hp, htau, hb]
  constructor
  · nlinarith only [hD, hM, hp2, hτ, hB0]
  · nlinarith only [hfhi, hp, htau, hb]

/-- If `B > 0`, `f ≤ 1`, `P ≥ 1`, and `τ ≥ 4`, a supply `M ≤ B * f`
and its mean budget imply `k ≤ τ`. Compare both sides after multiplication by `B`.
This supplies the logarithmic bound for the floor-selected subset size. -/
theorem mean_selected_size_le {B f τ P : ℝ} {M k : ℕ} (hB : 0 < B) (hf : f ≤ 1) (hP : 1 ≤ P)
    (hτ : 4 ≤ τ) (hM : (M : ℝ) ≤ B * f) (hmean : (k : ℝ) * (P * B) ≤ (τ - 4) * M) :
    (k : ℝ) ≤ τ := by
  have hM' : (M : ℝ) ≤ B := by
    have h := mul_le_mul_of_nonneg_left hf hB.le
    nlinarith only [hM, h]
  have h1 : 0 ≤ (P - 1) * (k : ℝ) * B :=
    mul_nonneg (mul_nonneg (by linarith only [hP]) (Nat.cast_nonneg k)) hB.le
  have h2 : 0 ≤ (τ - 4) * (B - M) := mul_nonneg (by linarith only [hτ]) (by linarith only [hM'])
  have hh : (k : ℝ) * B ≤ τ * B := by nlinarith only [hmean, h1, h2, hB]
  exact (mul_le_mul_iff_left₀ hB).mp hh

/-- If `0 < τ ≤ 4 * 10 ^ 10`, `1 ≤ k ≤ τ`, and `u ≤ 48`, the displayed sum of
logarithmic and floor losses is at most 120. Bound the logarithms by powers of two and
the reciprocal by one. This supplies the loss budget in the mean-gap criterion. -/
theorem mean_log_loss_le {τ u : ℝ} {k : ℕ} (hτ : 0 < τ) (hτU : τ ≤ 40000000000) (hk : 1 ≤ k)
    (hkle : (k : ℝ) ≤ τ) (hu : u ≤ 48) :
    Real.log τ - Real.log 4 + Real.log k / 2 + Real.log (2 * Real.pi) / 2 + 1 / (12 * (k : ℝ)) +
        2 * (u / 2 + 999 / 1000) ≤
      120 := by
  have hτpow : τ ≤ (2 : ℝ) ^ 36 := by
    norm_num only; linarith only [hτU]
  have hlog := Real.log_le_log hτ hτpow
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hτlog : Real.log τ ≤ 30 := by linarith only [hlog, Real.log_two_lt_d9]
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  have hklog := Real.log_le_log hk0 hkle
  have hlogfour : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num only)
  have hpi : Real.log (2 * Real.pi) ≤ 3 := by
    have h2pi : 0 < 2 * Real.pi := by nlinarith only [Real.pi_pos]
    have hp :=
      Real.log_le_log h2pi
        (show 2 * Real.pi ≤ (2 : ℝ) ^ 3 by
          norm_num only; linarith only [Real.pi_lt_four])
    rw [Real.log_pow] at hp
    norm_num only [Nat.cast_ofNat] at hp
    linarith only [hp, Real.log_two_lt_d9]
  have hinv : (1 : ℝ) / (12 * k) ≤ 1 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only) hk0)).mpr
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith only [hkr]
  linarith only [hτlog, hklog, hlogfour, hpi, hinv, hu]

/-- For `52000 ≤ b ≤ 26138000000`, the logarithm of `b ^ 2` lies in `[20, 48]`.
Compare the lower endpoint with `2 ^ 15` and certify the upper logarithm by a finite
rational Taylor bound. This supplies the common range for all three mean-counting cells. -/
theorem mean_log_radius_bounds {b : ℕ} (hb : 52000 ≤ b) (hbU : b ≤ 26138000000) :
    20 ≤ Real.log (b ^ 2 : ℕ) ∧ Real.log (b ^ 2 : ℕ) ≤ 48 := by
  have hbR : (52000 : ℝ) ≤ b := by exact_mod_cast hb
  have hbUR : (b : ℝ) ≤ 26138000000 := by exact_mod_cast hbU
  have hlo :=
    Real.log_le_log (show (0 : ℝ) < (2 : ℝ) ^ 15 by norm_num only)
      (show (2 : ℝ) ^ 15 ≤ b by
        norm_num only; linarith only [hbR])
  rw [Real.log_pow] at hlo
  norm_num only [Nat.cast_ofNat] at hlo
  have hc :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 26138000000 35 16 23 24 = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat] at hc
  have hhi := Real.log_le_log (show (0 : ℝ) < (b : ℝ) by linarith only [hbR]) hbUR
  have he : Real.log (b ^ 2 : ℕ) = 2 * Real.log (b : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  constructor
  · linarith only [hlo, Real.log_two_gt_d9, he]
  · linarith only [hhi, hc, he]

/-- If `0 < b ≤ 2 ^ j` and `2 * j * log 2 ≤ U`, then `log (b ^ 2) ≤ U`.
Apply logarithm monotonicity and the power identity. This gives compact upper bounds
for the first two mean-counting cells. -/
theorem mean_log_radius_of_pow {b j : ℕ} {U : ℝ} (hb : 0 < b) (hpow : b ≤ 2 ^ j)
    (hU : (2 : ℝ) * j * Real.log 2 ≤ U) : Real.log (b ^ 2 : ℕ) ≤ U := by
  have hb0 : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hp : (b : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hpow
  have hlog := Real.log_le_log hb0 hp
  rw [Real.log_pow] at hlog
  have he : Real.log (b ^ 2 : ℕ) = 2 * Real.log (b : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  nlinarith only [hlog, hU, he]

end PseudoPrime.PrimeTestBounds.MillerRabin
