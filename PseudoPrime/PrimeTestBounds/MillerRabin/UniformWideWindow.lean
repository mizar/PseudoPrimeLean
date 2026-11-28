/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltParameters

/-! # Coprime wide windows for uniform Korselt triples -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem ordered_factor_bounds {p q r a : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (ha : 1 ≤ a) (hap : a < p) (heq : a * (r - 1) = p * q - 1) (hd : q - 1 ∣ (p - 1) * (p + a)) :
    q < 2 * p ^ 2 ∧ r ≤ p ^ 3 := by
  have hp1 := Nat.sub_add_cancel hp.one_lt.le
  have hq1 := Nat.sub_add_cancel hq.one_lt.le
  have hr1 := Nat.sub_add_cancel hr.one_lt.le
  have hpq1 := Nat.sub_add_cancel (Nat.mul_pos hp.pos hq.pos)
  have hb :=
    Nat.le_of_dvd (Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (Nat.add_pos_left hp.pos a)) hd
  have hq' : q < 2 * p ^ 2 := by
    nlinarith only [hb, hq1, hp1, Nat.mul_lt_mul_of_pos_left hap hp.pos, hp.pos]
  have ha2 : 2 ≤ a := by
    by_contra! h
    have ha1 := Nat.le_antisymm (Nat.le_of_lt_succ h) ha
    rw [ha1, one_mul] at heq
    have hprod : r = p * q := by linarith only [heq, hr1, hpq1]
    exact (Nat.not_prime_mul hp.one_lt.ne' hq.one_lt.ne') (hprod ▸ hr)
  have hr' := Nat.mul_le_mul_right (r - 1) ha2
  exact ⟨hq', by nlinarith only [hr', heq, hr1, hpq1, Nat.mul_lt_mul_of_pos_left hq' hp.pos]⟩

/-- For an ordered uniform Korselt triple, its product is strictly less than
twice the sixth power of its least prime. The quotient parameter bounds the other
two factors and hence controls the coprime window for character sums. -/
theorem uniform_lt_twice_sixth {n p q r : ℕ} (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p < q) (hqr : q < r) (hu : UniformKorseltTriple n) : n < 2 * p ^ 6 := by
  obtain ⟨a, ha, hap, he, hd⟩ := uniformKorselt_ordered_parameters hn hp hq hr hpq hqr hu
  obtain ⟨hb, hc⟩ := ordered_factor_bounds hp hq hr ha hap he hd
  calc
    n = p * q * r := hn
    _ < (p * (2 * p ^ 2)) * r :=
      Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hb hp.pos) hr.pos
    _ ≤ (p * (2 * p ^ 2)) * p ^ 3 := Nat.mul_le_mul_left _ hc
    _ = 2 * p ^ 6 := by ring

private theorem exp_window {L scale : ℝ} (hL : 465 ≤ L) (hs : 0 ≤ scale) (hu : scale ≤ 26 / 25) :
    2 * ((scale * L / 2) ^ 4) ^ 6 ≤ Real.exp L := by
  have h0 : 0 ≤ L := le_trans (by norm_num only : (0 : ℝ) ≤ 465) hL
  have h := Real.pow_div_factorial_le_exp (L / 24) (div_nonneg h0 (by norm_num only)) 3
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_one,
    mul_one] at h
  have hpow := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 465) hL 2
  have hex : L ≤ Real.exp (L / 24) := by nlinarith only [h, h0, mul_le_mul_of_nonneg_right hpow h0]
  have he := pow_le_pow_left₀ h0 hex 24
  rw [← Real.exp_natCast_mul] at he
  have heq : (24 : ℝ) * (L / 24) = L := by ring
  rw [show ((24 : ℕ) : ℝ) * (L / 24) = L from heq] at he
  have hscaled : scale * L / 2 ≤ 3 / 4 * L := by
    apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    exact (mul_le_mul_of_nonneg_right hu h0).trans (by linarith only [h0])
  have hpow' := pow_le_pow_left₀ (div_nonneg (mul_nonneg hs h0) (by norm_num only)) hscaled 24
  rw [mul_pow] at hpow'
  rw [← pow_mul]
  norm_num only [Nat.reduceMul]
  exact
    (show 2 * (scale * L / 2) ^ 24 ≤ L ^ 24 from by linarith only [hpow', pow_nonneg h0 24]).trans
      he

/-- For an ordered uniform Korselt triple, the enlarged cutoff used by
the Gaussian comparisons still has square below the smallest prime factor. -/
theorem uniform_scaled_window_lt_prime {n p q r : ℕ} (hn : n = p * q * r) (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpq : p < q) (hqr : q < r) (hu : UniformKorseltTriple n)
    (hL : 465 ≤ Real.log n) {scale : ℝ} (hs : 0 ≤ scale) (hmax : scale ≤ 26 / 25) :
    (scale * Real.log n / 2) ^ 4 < (p : ℝ) := by
  have hnpos : 0 < n := hn ▸ Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos
  have hb : (n : ℝ) < 2 * (p : ℝ) ^ 6 := by
    exact_mod_cast uniform_lt_twice_sixth hn hp hq hr hpq hqr hu
  have hw := exp_window hL hs hmax
  rw [Real.exp_log (Nat.cast_pos.mpr hnpos)] at hw
  by_contra! h
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg p) h 6
  linarith only [hw, hb, hpow]

/-- If the logarithm of an ordered uniform Korselt triple is at least 465,
its least prime exceeds the square of the quarter-square cutoff. Combine the
sixth-power product bound with exponential growth to justify the wide window. -/
theorem uniform_wideWindow_lt_prime {n p q r : ℕ} (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p < q) (hqr : q < r) (hu : UniformKorseltTriple n)
    (hL : 465 ≤ Real.log n) : (Real.log n / 2) ^ 4 < (p : ℝ) := by
  simpa only [one_mul] using
    uniform_scaled_window_lt_prime hn hp hq hr hpq hqr hu hL (scale := 1) (by norm_num only)
      (by norm_num only)

/-- Every positive integer up to the square of the quarter cutoff is coprime to
a uniform Korselt triple of logarithm at least 465. The ordered least factor
exceeds the entire summation window, so each of the three factors is coprime. -/
theorem uniform_wideWindow_coprime {n m : ℕ} (hu : UniformKorseltTriple n) (hL : 465 ≤ Real.log n)
    (hm : 0 < m) (hwin : (m : ℝ) ≤ (Real.log n / 2) ^ 4) : m.Coprime n := by
  obtain ⟨p, q, r, hp, hq, hr, hpq, hqr, hn⟩ := uniform_korselt_ordered hu
  have hmp : m < p := by
    exact_mod_cast hwin.trans_lt (uniform_wideWindow_lt_prime hn hp hq hr hpq hqr hu hL)
  have cop {s : ℕ} (hs : s.Prime) (hlt : m < s) : m.Coprime s :=
    (hs.coprime_iff_not_dvd.mpr (fun hd => hlt.not_ge (Nat.le_of_dvd hm hd))).symm
  rw [hn]
  exact
    ((cop hp hmp).mul_right (cop hq (hmp.trans hpq))).mul_right (cop hr (hmp.trans (hpq.trans hqr)))

end PseudoPrime.PrimeTestBounds.MillerRabin
