/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighRadiusLogBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.HighSquarePrimeCount
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimePowerCountingCriteria
public import PseudoPrime.PrimeTestBounds.MillerRabin.MarkedFactorLogBounds
public import PseudoPrime.NumberTheory.UnitPowerCardinality

/-! # Paired-prime count budgets for the high-range coefficient -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Let `u` be positive and at most 48. If the logarithmic remainder
`u ^ 2 + (29 / 25) * u` is at most `L / 100`, and `k` is at least
`(66143 / 100000) * L / u - 1`, then a paired-base logarithm of at least
`u / 2 + 29 / 50` gives a strict count budget above `(33857 / 100000) * L`.
This scalar interface absorbs the ceiling error for the semiprime branch. -/
theorem highCoeff_semiprime_scalar {L u k : ℝ} (hL : 0 < L) (hu : 0 < u) (hu48 : u ≤ 48)
    (hm : u ^ 2 + (29 / 25 : ℝ) * u ≤ L / 100) (hk : (66143 / 100000 : ℝ) * L / u - 1 ≤ k) :
    (33857 / 100000 : ℝ) * L < k * (u / 2 + 29 / 50) := by
  have hpos : 0 ≤ u / 2 + (29 / 50 : ℝ) := by linarith only [hu]
  have hmul := mul_le_mul_of_nonneg_right hk hpos
  have hc : ((66143 / 100000 : ℝ) * L / u) * u = (66143 / 100000 : ℝ) * L :=
    div_mul_cancel₀ _ hu.ne'
  have hd := mul_nonneg (sub_nonneg.mpr hu48) hL.le
  have he :
    (29 / 50 : ℝ) * ((66143 / 100000 : ℝ) * L) - (1571 / 200000 : ℝ) * L * u >
      (u ^ 2 + (29 / 25 : ℝ) * u) / 2 := by
    nlinarith only [hd, hm, hL]
  have he' := (div_lt_div_iff_of_pos_right hu).2 he
  have heq : ((u ^ 2 + (29 / 25 : ℝ) * u) / 2) / u = u / 2 + 29 / 50 := by
    field_simp
    ring
  rw [heq] at he'
  have hx :
    ((29 / 50 : ℝ) * ((66143 / 100000 : ℝ) * L) - (1571 / 200000 : ℝ) * L * u) / u =
      (29 / 50 : ℝ) * ((66143 / 100000 : ℝ) * L / u) - (1571 / 200000 : ℝ) * L := by
    field_simp
  rw [hx] at he'
  nlinarith only [hmul, hc, he']

/-- If the paired binomial base is positive and its logarithm meets the scalar
budget, the binomial count exceeds the exponential kernel bound. This converts
the continuous semiprime budget into the existing prime-product counting interface. -/
theorem highCoeff_semiprime_choose {L u : ℝ} {M k : ℕ} (hL : 0 < L) (hu : 0 < u) (hu48 : u ≤ 48)
    (hm : u ^ 2 + (29 / 25 : ℝ) * u ≤ L / 100) (hk : (66143 / 100000 : ℝ) * L / u - 1 ≤ k)
    (hR : 0 < 2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1))
    (hlog : u / 2 + (29 / 50 : ℝ) ≤ Real.log (2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1))) :
    Real.exp ((33857 / 100000 : ℝ) * L) < (Nat.choose M k : ℝ) := by
  apply exp_lt_choose_of_paired_budget M k hR
  exact
    (highCoeff_semiprime_scalar hL hu hu48 hm hk).trans_le
      (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k))

/-- The exponential series at 24 exceeds the largest floor radius in the
bounded high-range semiprime argument. The 55-term partial sum gives a rational certificate. -/
private theorem highCoeff_exp_twentyFour : (26457200000 : ℝ) ≤ Real.exp 24 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 24) 55
  norm_num only [Finset.sum_range_succ, Nat.factorial, Nat.cast_ofNat] at h
  linarith only [h]

/-- For `70000 ≤ L ≤ 4 * 10 ^ 10`, twice the logarithm of the selected floor
radius is at most 48. The exponential certificate controls the upper endpoint. -/
theorem highCoeff_semiprime_log_le {L : ℝ} (hL : 70000 ≤ L) (hU : L ≤ 40000000000) :
    2 * Real.log (⌊(66143 / 100000 : ℝ) * L⌋₊ : ℝ) ≤ 48 := by
  have ha : 0 ≤ (66143 / 100000 : ℝ) * L := by linarith only [hL]
  have hf := Nat.floor_le ha
  have hlt := Nat.lt_floor_add_one ((66143 / 100000 : ℝ) * L)
  have hb : 0 < (⌊(66143 / 100000 : ℝ) * L⌋₊ : ℝ) := by linarith only [hL, hlt]
  have hbound : (⌊(66143 / 100000 : ℝ) * L⌋₊ : ℝ) ≤ 26457200000 := by linarith only [hf, hU]
  have hlog : Real.log (⌊(66143 / 100000 : ℝ) * L⌋₊ : ℝ) ≤ 24 :=
    (Real.log_le_iff_le_exp hb).mpr (hbound.trans highCoeff_exp_twentyFour)
  linarith only [hlog]

/-- From logarithmic scale 70000 onward, the selected floor radius has a
quadratic logarithmic remainder bounded by one hundredth of `L`.
The tangent logarithm estimate at `sqrt (L / 70000)` gives a uniform bound. -/
theorem highCoeff_semiprime_log_margin {L : ℝ} (hL : 70000 ≤ L) :
    let u := 2 * Real.log (⌊(66143 / 100000 : ℝ) * L⌋₊ : ℝ)
    u ^ 2 + (29 / 25 : ℝ) * u ≤ L / 100 := by
  dsimp only
  let b : ℝ := (⌊(66143 / 100000 : ℝ) * L⌋₊ : ℝ)
  have hlogbase : Real.log (70000 : ℝ) < 12 := by
    have h :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 70000) (by norm_num only : (70000 : ℝ) ≤ 2 ^ 17)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h, Real.log_two_lt_d9]
  have ha : 0 ≤ (66143 / 100000 : ℝ) * L := by linarith only [hL]
  have hf := Nat.floor_le ha
  have hlt := Nat.lt_floor_add_one ((66143 / 100000 : ℝ) * L)
  have hb : 1 ≤ b := by
    dsimp only [b]
    linarith only [hL, hlt]
  have hbL : b ≤ L := by
    dsimp only [b]
    linarith only [hL, hf]
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

/-- If the selected radius is within one of `(66143 / 100000) * L`,
the logarithmic scale is at most `L / 2000`, and the floor and ceiling
parameters satisfy their defining inequalities, the paired binomial base
exceeds `(179 / 100) * b`. This retains the small margin needed at the upper endpoint. -/
theorem highCoeff_semiprime_ratio {L b u : ℝ} {M k : ℕ} (hL : 70000 ≤ L)
    (hb : (66143 / 100000 : ℝ) * L - 1 ≤ b) (hu0 : 0 < u) (hu : u ≤ L / 2000) (hkM : k ≤ M)
    (hM : ((9 / 10 : ℝ) * b ^ 2) / u < (M : ℝ) + 1) (hk : (k : ℝ) < (66143 / 100000 : ℝ) * L / u) :
    (179 / 100 : ℝ) * b < 2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1) := by
  have hb0 : 0 < b := by linarith only [hL, hb]
  have hpart : (179 / 100 : ℝ) * ((66143 / 100000 : ℝ) * L + u) < (9 / 5 : ℝ) * b - 4 := by
    linarith only [hL, hb, hu]
  have hmul := mul_lt_mul_of_pos_left hpart hb0
  have hbound : 2 * ((66143 / 100000 : ℝ) * L) ≤ 4 * b := by linarith only [hL, hb]
  have hbase :
    (179 / 100 : ℝ) * b * ((66143 / 100000 : ℝ) * L + u) <
      2 * ((9 / 10 : ℝ) * b ^ 2 - (66143 / 100000 : ℝ) * L) := by
    nlinarith only [hmul, hbound]
  have hmk : ((M + 1 - k : ℕ) : ℝ) = (M : ℝ) + 1 - k := by
    rw [Nat.cast_sub (hkM.trans (Nat.le_succ M)), Nat.cast_succ]
  have hN : ((9 / 10 : ℝ) * b ^ 2 - (66143 / 100000 : ℝ) * L) < ((M + 1 - k : ℕ) : ℝ) * u := by
    have hm := (div_lt_iff₀ hu0).mp hM
    have hkk := (lt_div_iff₀ hu0).mp hk
    nlinarith only [hm, hkk, hmk]
  have hK : ((k : ℝ) + 1) * u < (66143 / 100000 : ℝ) * L + u := by
    have hkk := (lt_div_iff₀ hu0).mp hk
    linarith only [hkk]
  have hleft := mul_lt_mul_of_pos_left hK (mul_pos (by norm_num only : (0 : ℝ) < 179 / 100) hb0)
  have hright := mul_lt_mul_of_pos_left hN (show (0 : ℝ) < 2 by norm_num only)
  have hden : 0 < (k : ℝ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) (by norm_num only)
  apply (lt_div_iff₀ hden).2
  have hv : (179 / 100 : ℝ) * b * ((k : ℝ) + 1) * u < (2 * ((M + 1 - k : ℕ) : ℝ)) * u := by
    nlinarith only [hleft, hbase, hright]
  exact lt_of_mul_lt_mul_right hv hu0.le

/-- The logarithm of `179 / 100` is at least `29 / 50`. A rational
Taylor certificate supplies the constant needed by the paired-count budget. -/
private theorem highCoeff_log_ratio : (29 / 50 : ℝ) ≤ Real.log (179 / 100 : ℝ) := by
  have hc : Analysis.rationalLogIntervalCheck (179 / 100) 1 12 (29 / 50) 1 = true := by
    decide +kernel
  have h := (Analysis.rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

/-- At scale at least 70000, the quadratic logarithmic remainder bound implies
`u ≤ L / 2000` for nonnegative `u`. This absorbs floor and ceiling errors in
the paired-prime ratio estimate. -/
theorem highCoeff_semiprime_log_linear {L u : ℝ} (hL : 70000 ≤ L) (hu : 0 ≤ u)
    (hm : u ^ 2 + (29 / 25 : ℝ) * u ≤ L / 100) : u ≤ L / 2000 := by
  by_contra hnot
  have hx : L / 2000 < u := lt_of_not_ge hnot
  nlinarith only [hL, hu, hm, hx, sq_nonneg (u - L / 2000), sq_nonneg (L - 70000)]

/-- Throughout `70000 ≤ L ≤ 4 * 10 ^ 10`, the selected floor radius, prime
supply and ceiling-minus-one exponent make the paired binomial count exceed
`exp ((33857 / 100000) * L)`. The proof controls floor and ceiling errors
uniformly and needs no enumeration of individual inputs. -/
theorem highCoeff_semiprime_selected_count {L : ℝ} (hL : 70000 ≤ L) (hU : L ≤ 40000000000) :
    let b : ℝ := (⌊(66143 / 100000 : ℝ) * L⌋₊ : ℝ)
    let u := 2 * Real.log b
    let M := ⌊((9 / 10 : ℝ) * b ^ 2) / u⌋₊
    let k := ⌈(66143 / 100000 : ℝ) * L / u⌉₊ - 1
    Real.exp ((33857 / 100000 : ℝ) * L) < (Nat.choose M k : ℝ) := by
  dsimp only
  let b : ℝ := (⌊(66143 / 100000 : ℝ) * L⌋₊ : ℝ)
  let u := 2 * Real.log b
  let M := ⌊((9 / 10 : ℝ) * b ^ 2) / u⌋₊
  let k := ⌈(66143 / 100000 : ℝ) * L / u⌉₊ - 1
  have hL0 : 0 < L := by linarith only [hL]
  have hbFloor := Nat.lt_floor_add_one ((66143 / 100000 : ℝ) * L)
  have hb : (66143 / 100000 : ℝ) * L - 1 ≤ b := by
    dsimp only [b]
    linarith only [hbFloor]
  have hb1 : 1 < b := by linarith only [hL, hb]
  have hu : 0 < u := mul_pos (by norm_num only) (Real.log_pos hb1)
  have hm : u ^ 2 + (29 / 25 : ℝ) * u ≤ L / 100 := highCoeff_semiprime_log_margin hL
  have hu48 : u ≤ 48 := highCoeff_semiprime_log_le hL hU
  have huLin : u ≤ L / 2000 := highCoeff_semiprime_log_linear hL hu.le hm
  have hy : 0 < (66143 / 100000 : ℝ) * L / u := div_pos (mul_pos (by norm_num only) hL0) hu
  have hk := ceil_sub_one_bounds hy
  have hquad : (66143 / 100000 : ℝ) * L < (9 / 10 : ℝ) * b ^ 2 := by
    nlinarith only [hL, hb, sq_nonneg (b - 100)]
  have hkM : k ≤ M := ceil_sub_one_le_floor hy ((div_lt_div_iff_of_pos_right hu).2 hquad)
  have hfloor := Nat.lt_floor_add_one (((9 / 10 : ℝ) * b ^ 2) / u)
  have hratio : (179 / 100 : ℝ) * b < 2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1) :=
    highCoeff_semiprime_ratio hL hb hu huLin hkM hfloor hk.2
  have hpos : 0 < (179 / 100 : ℝ) * b :=
    mul_pos (by norm_num only) (lt_trans (by norm_num only) hb1)
  have hR : 0 < 2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1) := hpos.trans hratio
  have hlog := Real.log_lt_log hpos hratio
  rw [Real.log_mul (by norm_num only : (179 / 100 : ℝ) ≠ 0)
      (ne_of_gt (lt_trans (by norm_num only : (0 : ℝ) < 1) hb1))] at hlog
  have hbudget : u / 2 + (29 / 50 : ℝ) ≤ Real.log (2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1)) := by
    dsimp only [u]
    linarith only [hlog, highCoeff_log_ratio]
  exact highCoeff_semiprime_choose hL0 hu hu48 hm hk.1 hR hbudget

/-- For `n = m * q` with `m > 1` and prime `q`, logarithmic product and
count bounds yield both `B ^ k < q` and a local Fermat-kernel gcd smaller
than `C`. The cofactor need not be prime. -/
theorem highCoeff_cofactor_kernel {n m q B C k : ℕ} (hm : 1 < m) (hq : q.Prime) (hprod : n = m * q)
    (hB : 1 < B) (hsize : (k : ℝ) * Real.log B < Real.log q)
    (hcount : Real.log m < Real.log (C : ℝ)) : B ^ k < q ∧ (q - 1).gcd (n - 1) < C := by
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr hq.pos
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr (zero_lt_one.trans hB)
  have hlog : Real.log ((B : ℝ) ^ k) < Real.log (q : ℝ) := by
    rw [Real.log_pow]
    exact hsize
  have hreal : (B : ℝ) ^ k < q := (Real.log_lt_log_iff (pow_pos hBpos _) hqpos).mp hlog
  have hnat : B ^ k < q := by exact_mod_cast hreal
  have hcpos : 0 < C := by
    by_contra h
    have hz : C = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.cast_zero, Real.log_zero] at hcount
    exact (not_lt_of_ge (Real.log_natCast_nonneg m)) hcount
  have hmchoose : m < C := by
    exact_mod_cast
      (Real.log_lt_log_iff (Nat.cast_pos.mpr (zero_lt_one.trans hm)) (Nat.cast_pos.mpr hcpos)).mp
        hcount
  have hgcd : (q - 1).gcd (n - 1) ≤ m - 1 := by
    rw [hprod, Nat.mul_comm m q]
    exact NumberTheory.gcd_predecessor_product_le_cofactor hq.pos hm
  exact ⟨hnat, hgcd.trans_lt ((Nat.sub_le m 1).trans_lt hmchoose)⟩

/-- Under RH, for `n = m * q` with odd `n` and `m > 1`, a prime `q` whose logarithm
exceeds `(66143 / 100000) * log n` supplies a prime MR witness bounded by
`(7 / 16) * log n ^ 2` throughout the logarithmic interval from 70000 to
40 billion. The paired binomial count exceeds the local Fermat kernel. -/
theorem highCoeff_largeCofactor_witness {n m q : ℕ} (hn : 1 < n) (ho : Odd n) (hm : 1 < m)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = m * q) (hRH : RiemannHypothesis)
    (hL : (70000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 40000000000)
    (hqLarge : (66143 / 100000 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 16 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let L := Real.log n
  let b := ⌊(66143 / 100000 : ℝ) * L⌋₊
  let B := b ^ 2
  let u := 2 * Real.log (b : ℝ)
  let M := ⌊((9 / 10 : ℝ) * (b : ℝ) ^ 2) / u⌋₊
  let k := ⌈(66143 / 100000 : ℝ) * L / u⌉₊ - 1
  have hLf : 0 < L := by linarith only [hL]
  have hbFloor := Nat.lt_floor_add_one ((66143 / 100000 : ℝ) * L)
  have hbReal : (56 : ℝ) ≤ b := by
    dsimp only [b]
    linarith only [hL, hbFloor]
  have hb : 56 ≤ b := by exact_mod_cast hbReal
  have hB : 1 < B := by
    dsimp only [B]
    nlinarith only [hb]
  have hb1 : 1 < (b : ℝ) := by linarith only [hbReal]
  have hu : 0 < u := mul_pos (by norm_num only) (Real.log_pos hb1)
  have hy : 0 < (66143 / 100000 : ℝ) * L / u := div_pos (mul_pos (by norm_num only) hLf) hu
  have hk := (ceil_sub_one_bounds hy).2
  have hsize : (k : ℝ) * Real.log B < (66143 / 100000 : ℝ) * L := by
    have hs := (lt_div_iff₀ hu).mp hk
    dsimp only [B, u] at hs ⊢
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    exact hs
  have hpi : M ≤ B.primeCounting := by
    have h := high_square_floor_prime_count hRH hb
    simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using h
  have he := highCoeff_semiprime_selected_count hL hU
  have hc : (33857 / 100000 : ℝ) * L < Real.log (Nat.choose M k : ℝ) := by
    have ht := Real.log_lt_log (Real.exp_pos ((33857 / 100000 : ℝ) * L)) he
    simpa only [Real.log_exp] using ht
  have hlog : Real.log n = Real.log m + Real.log q := by
    rw [hprod, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt (zero_lt_one.trans hm)))
        (Nat.cast_ne_zero.mpr hq.ne_zero)]
  have hsmall : Real.log m < (33857 / 100000 : ℝ) * L := by linarith only [hlog, hqLarge]
  obtain ⟨hs, hc'⟩ :=
    highCoeff_cofactor_kernel hm hq hprod hB (hsize.trans hqLarge) (hsmall.trans hc)
  have hd : q ^ 1 ∣ n := by
    rw [pow_one, hprod]
    exact dvd_mul_left q m
  obtain ⟨r, hr, hbR, hf⟩ :=
    exists_prime_choose_count_gcd hn ho hq hq2 (by norm_num only : 0 < 1) hd B M k hpi
      (by simpa only [pow_one] using hs) hc'
  have hscale : 0 ≤ (66143 / 100000 : ℝ) * L := by linarith only [hL]
  have hfloor := Nat.floor_le hscale
  have hsquare := pow_le_pow_left₀ (Nat.cast_nonneg b) hfloor 2
  have hbound : (B : ℝ) ≤ (7 / 16 : ℝ) * L ^ 2 := by
    dsimp only [B]
    rw [Nat.cast_pow]
    nlinarith only [hsquare]
  exact ⟨r, hr, (Nat.cast_le.mpr hbR).trans hbound, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
