/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighPrimeSupply99
public import PseudoPrime.PrimeTestBounds.MillerRabin.HighCoefficientSemiprime

/-! # Variable-radius bounds for the large-cofactor branch -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For an odd `n = m * q` with prime `q`, a prime supply and product count exceeding the
cofactor budget yield a rejecting prime up to `B`. The logarithmic size condition puts each
selected product below the local modulus, allowing the gcd kernel criterion to apply. -/
theorem large_cofactor_witness_of_count {n m q B M k : ℕ} {α : ℝ} (hn : 1 < n) (ho : Odd n)
    (hm : 1 < m) (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = m * q) (hB : 1 < B)
    (hqLarge : α * Real.log n < Real.log q) (hpi : M ≤ B.primeCounting)
    (hsize : (k : ℝ) * Real.log B < α * Real.log n)
    (hcount : Real.exp ((1 - α) * Real.log n) < (Nat.choose M k : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hc : (1 - α) * Real.log n < Real.log (Nat.choose M k : ℝ) := by
    have ht := Real.log_lt_log (Real.exp_pos ((1 - α) * Real.log n)) hcount
    simpa only [Real.log_exp] using ht
  have hlog : Real.log n = Real.log m + Real.log q := by
    rw [hprod, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt (zero_lt_one.trans hm)))
        (Nat.cast_ne_zero.mpr hq.ne_zero)]
  have hsmall : Real.log m < (1 - α) * Real.log n := by linarith only [hlog, hqLarge]
  obtain ⟨hs, hc'⟩ :=
    highCoeff_cofactor_kernel hm hq hprod hB (hsize.trans hqLarge) (hsmall.trans hc)
  have hd : q ^ 1 ∣ n := by
    rw [pow_one, hprod]
    exact dvd_mul_left q m
  exact
    exists_prime_choose_count_gcd hn ho hq hq2 (by norm_num only : 0 < 1) hd B M k hpi
      (by simpa only [pow_one] using hs) hc'

/-- Under RH, the `99 / 100` supply and paired scalar gap give a rejecting prime for a large
prime cofactor. The supplied floor and ceiling inequalities control the square radius and the
product count; the bound is expressed using the variable coefficient `α ^ 2`. -/
theorem large_cofactor_witness_of_gap {n m q b M k : ℕ} {α u U : ℝ} (hn : 1 < n) (ho : Odd n)
    (hm : 1 < m) (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = m * q) (hRH : RiemannHypothesis)
    (hL : (70000 : ℝ) ≤ Real.log n) (hα : (647 / 1000 : ℝ) ≤ α) (hα2 : α ≤ 2 / 3) (hb : 5000 ≤ b)
    (hblo : α * Real.log n - 1 ≤ (b : ℝ)) (hbhi : (b : ℝ) ≤ α * Real.log n) (hu0 : 0 < u)
    (hu : u ≤ Real.log n / 2000) (huU : u ≤ U) (hlog : u = 2 * Real.log (b : ℝ)) (hkM : k ≤ M)
    (hMlo : ((99 / 100 : ℝ) * (b : ℝ) ^ 2) / u < (M : ℝ) + 1)
    (hMhi : (M : ℝ) * u ≤ (99 / 100 : ℝ) * (b : ℝ) ^ 2) (hklo : α * Real.log n / u - 1 ≤ (k : ℝ))
    (hkhi : (k : ℝ) < α * Real.log n / u) (hgap : (3 / 2 * α - 1) * U + (339 / 500) * α ≥ 1 / 100)
    (hmargin : u ^ 2 + (339 / 250) * u ≤ Real.log n / 100) (hqLarge : α * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ α ^ 2 * (Real.log n) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hB : 1 < b ^ 2 := by
    have hb2 : 2 ≤ b := by linarith only [hb]
    nlinarith only [hb2]
  have hlogB : Real.log (b ^ 2 : ℕ) = u := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    exact hlog.symm
  have hpi : M ≤ (b ^ 2).primeCounting := by
    apply high_square_prime_count_99 hRH hb
    rw [hlogB]
    exact hMhi
  have hsize : (k : ℝ) * Real.log (b ^ 2 : ℕ) < α * Real.log n := by
    rw [hlogB]
    exact (lt_div_iff₀ hu0).mp hkhi
  have hcount :=
    high_paired_count_of_gap hL hα hα2 hblo hu0 hu huU hkM hMlo hklo hkhi hlog hgap hmargin
  obtain ⟨r, hr, hrB, hrnot⟩ :=
    large_cofactor_witness_of_count hn ho hm hq hq2 hprod hB hqLarge hpi hsize hcount
  have hsquare := pow_le_pow_left₀ (Nat.cast_nonneg b) hbhi 2
  have hrreal : (r : ℝ) ≤ (b : ℝ) ^ 2 := by exact_mod_cast hrB
  have hbound : (r : ℝ) ≤ α ^ 2 * (Real.log n) ^ 2 := by nlinarith only [hrreal, hsquare]
  exact ⟨r, hr, hbound, hrnot⟩

/-- For a large prime cofactor, the selected floor radius and ceiling-minus-one exponent give
an MR witness at the variable squared radius once the logarithmic and scalar gap bounds hold.
The `99 / 100` prime supply and all floor and ceiling estimates are derived internally. -/
theorem large_cofactor_witness_selected {n m q : ℕ} {α U : ℝ} (hn : 1 < n) (ho : Odd n) (hm : 1 < m)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = m * q) (hRH : RiemannHypothesis)
    (hL : (70000 : ℝ) ≤ Real.log n) (hα : (647 / 1000 : ℝ) ≤ α) (hα2 : α ≤ 2 / 3)
    (hu : 2 * Real.log (⌊α * Real.log n⌋₊ : ℝ) ≤ Real.log n / 2000)
    (huU : 2 * Real.log (⌊α * Real.log n⌋₊ : ℝ) ≤ U)
    (hgap : (3 / 2 * α - 1) * U + (339 / 500) * α ≥ 1 / 100)
    (hmargin :
      (2 * Real.log (⌊α * Real.log n⌋₊ : ℝ)) ^ 2 +
          (339 / 250) * (2 * Real.log (⌊α * Real.log n⌋₊ : ℝ)) ≤
        Real.log n / 100)
    (hqLarge : α * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ α ^ 2 * (Real.log n) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let L := Real.log n
  let b := ⌊α * L⌋₊
  let v := 2 * Real.log (b : ℝ)
  let M := ⌊((99 / 100 : ℝ) * (b : ℝ) ^ 2) / v⌋₊
  let k := ⌈α * L / v⌉₊ - 1
  have hL0 : 0 < L := by linarith only [hL]
  have hα0 : 0 < α := by linarith only [hα]
  have hb : 5000 ≤ b := high_floor_radius_ge_5000 hL hα
  have hb0 : 1 < (b : ℝ) := by
    have hbr : (5000 : ℝ) ≤ b := Nat.cast_le.mpr hb
    linarith only [hbr]
  have hv : 0 < v := mul_pos (by norm_num only) (Real.log_pos hb0)
  have hfloor := Nat.lt_floor_add_one (α * L)
  have hblo : α * L - 1 ≤ (b : ℝ) := by linarith only [hfloor]
  have hbhi : (b : ℝ) ≤ α * L := Nat.floor_le (mul_nonneg hα0.le hL0.le)
  have hy : 0 < α * L / v := div_pos (mul_pos hα0 hL0) hv
  have hk := ceil_sub_one_bounds hy
  have hquad : α * L < (99 / 100 : ℝ) * (b : ℝ) ^ 2 := by
    have hbr : (5000 : ℝ) ≤ b := Nat.cast_le.mpr hb
    nlinarith only [hblo, hbr, sq_nonneg ((b : ℝ) - 5000)]
  have hkM : k ≤ M := ceil_sub_one_le_floor hy ((div_lt_div_iff_of_pos_right hv).2 hquad)
  have hMlo : ((99 / 100 : ℝ) * (b : ℝ) ^ 2) / v < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hdiv0 : 0 ≤ ((99 / 100 : ℝ) * (b : ℝ) ^ 2) / v :=
    div_nonneg (mul_nonneg (by norm_num only) (sq_nonneg _)) hv.le
  have hMhi : (M : ℝ) * v ≤ (99 / 100 : ℝ) * (b : ℝ) ^ 2 := by
    have hf := Nat.floor_le hdiv0
    have hh := mul_le_mul_of_nonneg_right hf hv.le
    rw [div_mul_cancel₀ _ hv.ne'] at hh
    exact hh
  exact
    large_cofactor_witness_of_gap hn ho hm hq hq2 hprod hRH hL hα hα2 hb hblo hbhi hv hu huU rfl hkM
      hMlo hMhi hk.1 hk.2 hgap hmargin hqLarge

/-- For `L ≥ 70000` and `1 ≤ b ≤ L`, the quadratic logarithmic rounding budget needed by the
paired-prime count is at most `L / 100`. A tangent bound for the logarithm at the square-root
scale gives a uniform estimate over the whole half-line. -/
theorem high_variable_log_margin {L b : ℝ} (hL : 70000 ≤ L) (hb : 1 ≤ b) (hbL : b ≤ L) :
    (2 * Real.log b) ^ 2 + (339 / 250) * (2 * Real.log b) ≤ L / 100 := by
  have hlogbase : Real.log (70000 : ℝ) < 12 := by
    have h :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 70000) (by norm_num only : (70000 : ℝ) ≤ 2 ^ 17)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h, Real.log_two_lt_d9]
  have hlog := Real.log_le_log (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hb) hbL
  have hu0 : 0 ≤ 2 * Real.log b := mul_nonneg (by norm_num only) (Real.log_nonneg hb)
  have hr : (1 : ℝ) ≤ L / 70000 := by linarith only [hL]
  have hrpos : 0 < L / 70000 := by linarith only [hr]
  have hs1 : 1 ≤ Real.sqrt (L / 70000) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hr
  have ht := Real.log_le_sub_one_of_pos (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hs1)
  have hslog := Real.log_sqrt hrpos.le
  have he : Real.log L = Real.log (L / 70000) + Real.log 70000 := by
    rw [← Real.log_mul hrpos.ne' (by norm_num only : (70000 : ℝ) ≠ 0)]
    congr 1
    ring
  have hupper : 2 * Real.log b ≤ 20 + 4 * Real.sqrt (L / 70000) := by
    linarith only [hlogbase, hlog, ht, hslog, he]
  have hs2 := Real.sq_sqrt (show 0 ≤ L / 70000 by linarith only [hr])
  have hu2 := pow_le_pow_left₀ hu0 hupper 2
  nlinarith only [hupper, hu2, hs1, hs2, sq_nonneg (Real.sqrt (L / 70000) - 1)]

end PseudoPrime.PrimeTestBounds.MillerRabin
