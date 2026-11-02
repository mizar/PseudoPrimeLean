/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsHighCounting
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsHighPrimeCount
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsHighKernel

/-! # High-range prime supply for the selected floor radius -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH and `L ≥ 1024`, the floor count used by the high-range
construction is bounded by the number of primes up to the chosen square
radius. The floor radius is at least 56, so the uniform square-radius prime
supply applies. This is independent of any finite certificate table. -/
theorem high_floor_radius_prime_count (hRH : RiemannHypothesis) {L : ℝ} (hL : 1024 ≤ L) :
    ⌊((9 / 10 : ℝ) * (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ) ^ 2) / Real.log ((⌊(2 / 3 : ℝ) * L⌋₊ : ℕ) ^ 2)⌋₊ ≤
      ((⌊(2 / 3 : ℝ) * L⌋₊ : ℕ) ^ 2).primeCounting := by
  simpa only [Nat.cast_pow] using high_square_floor_prime_count hRH (high_radius_floor_lower hL).2.2

/-- The selected high-range exponent makes `k * log B < σ * L`, and the
selected binomial coefficient has logarithm exceeding `σ * L / 2`.
The strict ceiling bound gives the first inequality; the uniform paired-factor
kernel budget and logarithm monotonicity give the second. -/
theorem high_selected_log_budgets {L σ : ℝ} (hL : 1024 ≤ L) (hσ : (2 / 3 : ℝ) ≤ σ) (hσ1 : σ ≤ 1) :
    let b := ⌊(2 / 3 : ℝ) * L⌋₊
    let B := b ^ 2
    let u := 2 * Real.log (b : ℝ)
    let M := ⌊((9 / 10 : ℝ) * (b : ℝ) ^ 2) / u⌋₊
    let k := ⌈σ * L / u⌉₊ - 1
    (k : ℝ) * Real.log B < σ * L ∧ σ * L / 2 < Real.log (Nat.choose M k : ℝ) := by
  dsimp only
  let b := ⌊(2 / 3 : ℝ) * L⌋₊
  let B := b ^ 2
  let u := 2 * Real.log (b : ℝ)
  let M := ⌊((9 / 10 : ℝ) * (b : ℝ) ^ 2) / u⌋₊
  let k := ⌈σ * L / u⌉₊ - 1
  have hb : 1 < (b : ℝ) := by
    have hf := (high_radius_floor_lower hL).2.1
    linarith only [hL, hf]
  have hu : 0 < u := mul_pos (by norm_num only) (Real.log_pos hb)
  have hσ0 : 0 < σ := by linarith only [hσ]
  have hL0 : 0 < L := by linarith only [hL]
  have hy : 0 < σ * L / u := div_pos (mul_pos hσ0 hL0) hu
  have hk : (k : ℝ) < σ * L / u := (ceil_sub_one_bounds hy).2
  have hsize : (k : ℝ) * u < σ * L := (lt_div_iff₀ hu).mp hk
  have hlog : Real.log (B : ℝ) = u := by
    dsimp only [B, u]
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have he : Real.exp (σ * L / 2) < (Nat.choose M k : ℝ) := high_selected_choose_gt_exp hL hσ hσ1
  have hc : σ * L / 2 < Real.log (Nat.choose M k : ℝ) := by
    have ht := Real.log_lt_log (Real.exp_pos (σ * L / 2)) he
    simpa only [Real.log_exp] using ht
  exact
    ⟨by
      rw [hlog]; exact hsize, hc⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
