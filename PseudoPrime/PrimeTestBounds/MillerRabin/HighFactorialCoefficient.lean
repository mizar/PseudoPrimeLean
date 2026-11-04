/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighFactorialCounting
public import PseudoPrime.PrimeTestBounds.MillerRabin.HighVariableRepeated

/-! # Factorial-based variable coefficient and logarithmic budget -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The factorial-based radius coefficient at logarithmic scale `U`. It solves the strengthened
cofactor counting gap with margin `3 / 200`; its intended input is `2 * log L`. -/
noncomputable def factorialAlpha (U : ℝ) : ℝ :=
  (U + 3 / 200) / ((3 / 2) * U + 49 / 50)

/-- For `U ≥ 22`, the factorial coefficient lies between `647 / 1000` and `2 / 3`. Clearing the
positive denominator reduces both estimates to rational linear inequalities. -/
theorem factorialAlpha_bounds {U : ℝ} (hU : 22 ≤ U) :
    (647 / 1000 : ℝ) ≤ factorialAlpha U ∧ factorialAlpha U ≤ 2 / 3 := by
  have hd : 0 < (3 / 2 : ℝ) * U + 49 / 50 := by linarith only [hU]
  dsimp only [factorialAlpha]
  constructor
  · apply (le_div_iff₀ hd).mpr
    linarith only [hU]
  · apply (div_le_iff₀ hd).mpr
    linarith only [hU]

/-- For `U ≥ 22`, the factorial coefficient attains the exact `3 / 200` counting gap. This
identity is the scalar input for the factorial cofactor budget. -/
theorem factorialAlpha_gap {U : ℝ} (hU : 22 ≤ U) :
    (3 / 2 * factorialAlpha U - 1) * U + (49 / 50) * factorialAlpha U = 3 / 200 := by
  have hd : (3 / 2 : ℝ) * U + 49 / 50 ≠ 0 := by
    have hp : 0 < (3 / 2 : ℝ) * U + 49 / 50 := by linarith only [hU]
    exact hp.ne'
  have he : factorialAlpha U * ((3 / 2 : ℝ) * U + 49 / 50) = U + 3 / 200 := by
    dsimp only [factorialAlpha]
    exact div_mul_cancel₀ _ hd
  nlinarith only [he]

/-- For `L ≥ 70000` and `1 ≤ b ≤ L`, the factorial logarithmic rounding budget is at most
`L / 70`. The tangent logarithm estimate uniformly controls both the square and linear terms. -/
theorem factorial_log_margin {L b : ℝ} (hL : 70000 ≤ L) (hb : 1 ≤ b) (hbL : b ≤ L) :
    (3 / 2 : ℝ) * (2 * Real.log b) ^ 2 + (49 / 50) * (2 * Real.log b) ≤ L / 70 := by
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

/-- Under RH, the factorial coefficient gives a rejecting prime in the large-prime-cofactor
branch for `log n ≥ 70000`. The chosen floor radius and ceiling exponent satisfy the factorial
counting budget, including its logarithmic rounding loss. -/
theorem factorial_large_cofactor_witness {n m q : ℕ} (hn : 1 < n) (ho : Odd n) (hm : 1 < m)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = m * q) (hRH : RiemannHypothesis)
    (hL : (70000 : ℝ) ≤ Real.log n)
    (hqLarge : factorialAlpha (2 * Real.log (Real.log n)) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (factorialAlpha (2 * Real.log (Real.log n))) ^ 2 * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let L := Real.log n
  let U := 2 * Real.log L
  let α := factorialAlpha U
  let b := ⌊α * L⌋₊
  let B := b ^ 2
  let u := 2 * Real.log (b : ℝ)
  let M := ⌊((99 / 100 : ℝ) * (b : ℝ) ^ 2) / u⌋₊
  let k := ⌈α * L / u⌉₊ - 1
  have hL0 : 0 < L := by linarith only [hL]
  have hU : 22 ≤ U := high_log_twice_ge_22 hL
  have hα := factorialAlpha_bounds hU
  have hα0 : 0 < α := by linarith only [hα.1]
  have hb : 5000 ≤ b := high_floor_radius_ge_5000 hL hα.1
  have hbReal : (5000 : ℝ) ≤ b := Nat.cast_le.mpr hb
  have hb1 : 1 < (b : ℝ) := by linarith only [hbReal]
  have hfloor := Nat.lt_floor_add_one (α * L)
  have hblo : α * L - 1 ≤ (b : ℝ) := by linarith only [hfloor]
  have hbhi : (b : ℝ) ≤ α * L := Nat.floor_le (mul_nonneg hα0.le hL0.le)
  have hbL : (b : ℝ) ≤ L := by
    have hh := mul_le_mul_of_nonneg_right hα.2 hL0.le
    linarith only [hbhi, hh]
  have hu0 : 0 < u := mul_pos (by norm_num only) (Real.log_pos hb1)
  have hmargin := factorial_log_margin hL hb1.le hbL
  have hweak := high_variable_log_margin hL hb1.le hbL
  have hweak' : u ^ 2 + (29 / 25 : ℝ) * u ≤ L / 100 := by linarith only [hweak, hu0]
  have hu := highCoeff_semiprime_log_linear hL hu0.le hweak'
  have hlog := Real.log_le_log (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hb1.le) hbL
  have huU : u ≤ U := by linarith only [hlog]
  have hy : 0 < α * L / u := div_pos (mul_pos hα0 hL0) hu0
  have hk := ceil_sub_one_bounds hy
  have hquad : α * L < (99 / 100 : ℝ) * (b : ℝ) ^ 2 := by
    nlinarith only [hblo, hbReal, sq_nonneg ((b : ℝ) - 5000)]
  have hkM : k ≤ M := ceil_sub_one_le_floor hy ((div_lt_div_iff_of_pos_right hu0).2 hquad)
  have hMlo : ((99 / 100 : ℝ) * (b : ℝ) ^ 2) / u < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hu1 : 1 ≤ u := by
    have hh :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 2) (show (2 : ℝ) ≤ b by linarith only [hbReal])
    linarith only [hh, Real.log_two_gt_d9]
  have hklt := (lt_div_iff₀ hu0).mp hk.2
  have hkone : (k : ℝ) < α * L := by
    have hh := mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) (show 0 ≤ u - 1 by linarith only [hu1])
    nlinarith only [hh, hklt]
  have hksq : (k : ℝ) + 1 ≤ (b : ℝ) ^ 2 := by
    nlinarith only [hkone, hfloor, hbReal, sq_nonneg ((b : ℝ) - 2)]
  have hlogk : Real.log ((k : ℝ) + 1) ≤ u := by
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by linarith only [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hh := Real.log_le_log hkpos hksq
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have hgap := (factorialAlpha_gap hU).ge
  have hcount :=
    factorial_count_of_gap hL hα.1 hα.2 hblo hu0 hu huU hkM hMlo hk.1 hk.2 rfl hlogk hgap hmargin
  have hB : 1 < B := by
    dsimp only [B]
    nlinarith only [hb]
  have hpi : M ≤ B.primeCounting := by
    have hh := high_square_floor_prime_count_99 hRH hb
    simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using hh
  have hsize : (k : ℝ) * Real.log B < α * L := by
    dsimp only [B, u]
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    exact hklt
  obtain ⟨r, hr, hrB, hrnot⟩ :=
    large_cofactor_witness_of_count hn ho hm hq hq2 hprod hB hqLarge hpi hsize hcount
  have hsquare := pow_le_pow_left₀ (Nat.cast_nonneg b) hbhi 2
  have hrreal : (r : ℝ) ≤ (b : ℝ) ^ 2 := by exact_mod_cast hrB
  have hbound : (r : ℝ) ≤ α ^ 2 * L ^ 2 := by nlinarith only [hrreal, hsquare]
  exact ⟨r, hr, hbound, hrnot⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
