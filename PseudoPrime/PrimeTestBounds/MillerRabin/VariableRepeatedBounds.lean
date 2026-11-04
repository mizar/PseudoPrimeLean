/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighFactorialRepeated

/-! # Repeated-factor counting with a variable radius -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `L ≥ 70000`, `1 / 3 ≤ σ ≤ 1` and `647 / 1000 ≤ α ≤ 2 / 3`,
the displayed floor-selected prime-product count exceeds `exp (σ * L / 2)`.
The paired-factor estimate and the `7 / 6` base margin absorb the rounding losses.
This supplies the prime-power divisor argument at any radius in the allowed range. -/
theorem variable_partial_selected_count {L σ α : ℝ} (hL : 70000 ≤ L) (hα : (647 / 1000 : ℝ) ≤ α)
    (hα2 : α ≤ 2 / 3) (hσ : (1 / 3 : ℝ) ≤ σ) (hσ1 : σ ≤ 1) :
    let b : ℝ := (⌊α * L⌋₊ : ℝ)
    let u := 2 * Real.log b
    let M := ⌊((99 / 100 : ℝ) * b ^ 2) / u⌋₊
    let k := ⌈σ * L / u⌉₊ - 1
    Real.exp (σ * L / 2) < (Nat.choose M k : ℝ) := by
  dsimp only
  let b : ℝ := (⌊α * L⌋₊ : ℝ)
  let u := 2 * Real.log b
  let M := ⌊((99 / 100 : ℝ) * b ^ 2) / u⌋₊
  let k := ⌈σ * L / u⌉₊ - 1
  let R : ℝ := 2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1)
  have hL0 : 0 < L := by linarith only [hL]
  have hσ0 : 0 < σ := by linarith only [hσ]
  have hσL : σ * L ≤ L := by nlinarith only [mul_nonneg (sub_nonneg.mpr hσ1) hL0.le]
  have hα0 : 0 ≤ α := by linarith only [hα]
  have hαL := mul_le_mul_of_nonneg_right hα hL0.le
  have hbFloor := Nat.lt_floor_add_one (α * L)
  have hb : α * L - 1 ≤ b := by linarith only [hbFloor]
  have hb1 : 1 < b := by linarith only [hL, hαL, hb]
  have hbUpper := Nat.floor_le (mul_nonneg hα0 hL0.le)
  have hbL : b ≤ L := by
    have hh := mul_le_mul_of_nonneg_right hα2 hL0.le
    linarith only [hbUpper, hh]
  have hu : 0 < u := mul_pos (by norm_num only) (Real.log_pos hb1)
  have hm99 := high_variable_log_margin hL hb1.le hbL
  have hm : u ^ 2 + (29 / 25 : ℝ) * u ≤ L / 100 := by linarith only [hm99, hu]
  have huLin : u ≤ L / 2000 := highCoeff_semiprime_log_linear hL hu.le hm
  have hy : 0 < σ * L / u := div_pos (mul_pos hσ0 hL0) hu
  have hk := ceil_sub_one_bounds hy
  have hquad : σ * L < (99 / 100 : ℝ) * b ^ 2 := by
    nlinarith only [hL, hb, hαL, hσL, sq_nonneg (b - 100)]
  have hkM : k ≤ M := ceil_sub_one_le_floor hy ((div_lt_div_iff_of_pos_right hu).2 hquad)
  have hfloor := Nat.lt_floor_add_one (((99 / 100 : ℝ) * b ^ 2) / u)
  have hkUpper : (k : ℝ) < L / u := hk.2.trans_le ((div_le_div_iff_of_pos_right hu).2 hσL)
  have hratio : (7 / 6 : ℝ) * b < R := factorial_partial_ratio hL hα hb hu huLin hkM hfloor hkUpper
  have hpos : 0 < (7 / 6 : ℝ) * b := mul_pos (by norm_num only) (lt_trans (by norm_num only) hb1)
  have hR : 0 < R := hpos.trans hratio
  have hlog := Real.log_lt_log hpos hratio
  rw [Real.log_mul (by norm_num only : (7 / 6 : ℝ) ≠ 0)
      (ne_of_gt (lt_trans (by norm_num only : (0 : ℝ) < 1) hb1))] at hlog
  have hc : Analysis.rationalLogIntervalCheck (7 / 6) 0 12 (151 / 1000) 1 = true := by
    decide +kernel
  have hconst := (Analysis.rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hconst
  have hlogR : u / 2 + (3 / 20 : ℝ) < Real.log R := by
    dsimp only [u]
    linarith only [hlog, hconst]
  have hscalar := highCoeff_partial_scalar hL0 hσ hu hm hk.1
  have hkpos : 0 < k := by
    have hku := hk.1
    have hratio : (2 : ℝ) < σ * L / u := by
      apply (lt_div_iff₀ hu).2
      nlinarith only [hL, huLin, mul_nonneg (sub_nonneg.mpr hσ) hL0.le]
    have hkr : (0 : ℝ) < (k : ℝ) := by linarith only [hku, hratio]
    exact_mod_cast hkr
  have hmul := mul_lt_mul_of_pos_left hlogR (Nat.cast_pos.mpr hkpos)
  have hbudget : σ * L / 2 < (k : ℝ) * Real.log R := hscalar.trans hmul
  exact exp_lt_choose_of_paired_budget M k hR hbudget

/-- Under RH, a prime-power divisor of an odd `n > 1` whose logarithm lies between
`log n / 3` and `log n` yields a rejecting prime within `α ^ 2 * log n ^ 2`.
Here `647 / 1000 ≤ α ≤ 2 / 3` and `log n ≥ 70000`. The variable paired count
exceeds the local prime-power kernel. This handles repeated factors at the chosen radius. -/
theorem variable_primePow_divisor {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 2 ≤ a) (hdiv : p ^ a ∣ n) (hRH : RiemannHypothesis) {α : ℝ} (hα : (647 / 1000 : ℝ) ≤ α)
    (hα2 : α ≤ 2 / 3) (hL : (70000 : ℝ) ≤ Real.log n)
    (hlower : Real.log n / 3 ≤ Real.log (p ^ a : ℕ)) (hupper : Real.log (p ^ a : ℕ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ α ^ 2 * (Real.log n) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let L := Real.log n
  let σ := Real.log (p ^ a : ℕ) / L
  let b := ⌊α * L⌋₊
  let B := b ^ 2
  let u := 2 * Real.log (b : ℝ)
  let M := ⌊((99 / 100 : ℝ) * (b : ℝ) ^ 2) / u⌋₊
  let k := ⌈σ * L / u⌉₊ - 1
  have hLf : 0 < L := by linarith only [hL]
  have hσL : σ * L = Real.log (p ^ a : ℕ) := div_mul_cancel₀ _ hLf.ne'
  have hσ : (1 / 3 : ℝ) ≤ σ := by
    dsimp only [σ]
    apply (le_div_iff₀ hLf).mpr
    linarith only [hlower]
  have hσ1 : σ ≤ 1 := by
    dsimp only [σ]
    apply (div_le_iff₀ hLf).mpr
    linarith only [hupper]
  have hσ0 : 0 < σ := by linarith only [hσ]
  have hα0 : 0 ≤ α := by linarith only [hα]
  have hb : 5000 ≤ b := high_floor_radius_ge_5000 hL (by linarith only [hα])
  have hbReal : (5000 : ℝ) ≤ b := Nat.cast_le.mpr hb
  have hB : 1 < B := by
    dsimp only [B]
    nlinarith only [hb]
  have hb1 : 1 < (b : ℝ) := by linarith only [hbReal]
  have hu : 0 < u := mul_pos (by norm_num only) (Real.log_pos hb1)
  have hy : 0 < σ * L / u := div_pos (mul_pos hσ0 hLf) hu
  have hk := (ceil_sub_one_bounds hy).2
  have hsize : (k : ℝ) * Real.log B < Real.log (p ^ a : ℕ) := by
    have hs := (lt_div_iff₀ hu).mp hk
    dsimp only [B, u] at hs ⊢
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hs, hσL]
  have hpi : M ≤ B.primeCounting := by
    have h := high_square_floor_prime_count_99 hRH hb
    simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using h
  have he := variable_partial_selected_count hL hα hα2 hσ hσ1
  have hc : Real.log (p ^ a : ℕ) < 2 * Real.log (Nat.choose M k : ℝ) := by
    have ht := Real.log_lt_log (Real.exp_pos (σ * L / 2)) he
    rw [Real.log_exp] at ht
    linarith only [ht, hσL]
  obtain ⟨hs, hc'⟩ := highCoeff_primePow_choose hp (rfl : p ^ a = p ^ a) ha hB hsize hc
  obtain ⟨r, hr, hbR, hf⟩ :=
    exists_prime_primePow_choose_count hn ho hp hp2 (lt_of_lt_of_le (by norm_num only : 0 < 2) ha)
      hdiv B M k hpi hs hc'
  have hscale : 0 ≤ α * L := mul_nonneg hα0 hLf.le
  have hfloor := Nat.floor_le hscale
  have hsquare := pow_le_pow_left₀ (Nat.cast_nonneg b) hfloor 2
  have hbound : (B : ℝ) ≤ α ^ 2 * L ^ 2 := by
    dsimp only [B]
    rw [Nat.cast_pow]
    nlinarith only [hsquare]
  exact ⟨r, hr, (Nat.cast_le.mpr hbR).trans hbound, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
