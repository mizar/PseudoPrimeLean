/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedCap570

/-! # Uniform reflected kernel bound for the section 31 interval -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational upper bound for the logarithm of the prefix cutoff. -/
private theorem logB : Real.log 2701 ≤ 790138 / 100000 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 2701) (j := 11) (n := 20) (lo := 0) (hi :=
        790138 / 100000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] at h
  linarith only [h]

/-- Bound the logarithm at one million using its sixth-power representation. -/
private theorem logV : Real.log 1000000 ≤ 13816 / 1000 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 10) (j := 3) (n := 16) (lo := 0) (hi :=
        23026 / 10000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] at h
  rw [show (1000000 : ℝ) = 10 ^ 6 by norm_num only, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h]

/-- A rational upper enclosure for the main endpoint power at 2701. -/
private theorem mainB : (2701 : ℝ) ^ (-(13 / 25 : ℝ)) ≤ 16428852 / 1000000000 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 2701) (p := 13) (d :=
        25) (lo := 0) (hi := 16428852 / 1000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  linarith only [h]

/-- A rational upper enclosure for the error endpoint power at 2701. -/
private theorem errB : (2701 : ℝ) ^ (-(51 / 50 : ℝ)) ≤ 316115 / 1000000000 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 2701) (p := 51) (d :=
        50) (lo := 0) (hi := 316115 / 1000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  linarith only [h]

/-- A rational upper enclosure for the error endpoint power at one million. -/
private theorem errV : (1000000 : ℝ) ^ (-(51 / 50 : ℝ)) ≤ 75858 / 100000000000 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1000000) (p := 51) (d :=
        50) (lo := 0) (hi := 75858 / 100000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  linarith only [h]

/-- An explicit upper bound for the complementary moment, using rational endpoint data. -/
private noncomputable def capRat (j : ℕ) : ℝ :=
  let z : ℝ := 790138 / 100000
  let p : ℝ := 316115 / 1000000000
  16428852 / 1000000000 * Analysis.logPowerTailPoly (13 / 25) j z + 4 / 5 * p * z ^ j +
    (4 / 5 * (38 / 25)) * (p * Analysis.logPowerTailPoly (51 / 50) j z) +
    (38 / 25 / 24) *
      (75858 / 100000000000 * Analysis.logPowerTailPoly (51 / 50) (j + 2) (13816 / 1000))

/-- Nonnegativity and monotonicity of the tail polynomial propagate power and log upper bounds. -/
private theorem value_le {d x p z : ℝ} (hd : 0 < d) (hx : 1 ≤ x) (hp : x ^ (-d) ≤ p)
    (hz : Real.log x ≤ z) (j : ℕ) :
    eulerMomentValue570 d j x ≤ p * Analysis.logPowerTailPoly d j z := by
  exact
    mul_le_mul hp (Analysis.log_power_tail_poly_mono hd (Real.log_nonneg hx) hz j)
      (Analysis.log_power_tail_poly_nonneg hd (Real.log_nonneg hx) j)
      ((Real.rpow_nonneg (zero_le_one.trans hx) _).trans hp)

/-- Substituting the certified endpoints bounds each degree's complementary moment. -/
private theorem cap_le (j : ℕ) : reflectedCap570 j ≤ capRat j := by
  have h0 := value_le (by norm_num only) (by norm_num only) mainB logB j
  have h1 := value_le (by norm_num only) (by norm_num only) errB logB j
  have h2 := value_le (by norm_num only) (by norm_num only) errV logV (j + 2)
  have he : Real.sqrt 2701 * (2701 : ℝ) ^ (-(13 / 25 : ℝ) - 1) = 2701 ^ (-(51 / 50 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num only : (0 : ℝ) < 2701)]
    norm_num only
  have hlog := Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2701)
  have hm := mul_le_mul errB (pow_le_pow_left₀ hlog logB j) (pow_nonneg hlog j) (by norm_num only)
  unfold reflectedCap570 capRat eulerMoment570
  linear_combination
    h0 + (4 / 5 * (38 / 25)) * h1 + (38 / 25 / 24) * h2 + (4 / 5) * hm +
      (4 / 5 * Real.log 2701 ^ j) * he

/-- Rational upper bounds for the six signed coefficients in ascending moment degree. -/
noncomputable def reflectedCoeff570 : ℕ → ℝ
  | 0 => -41629 / 10000
  | 1 => -94124 / 10000
  | 2 => -297408 / 10000
  | 3 => -109515 / 1000
  | 4 => -31947 / 100
  | 5 => 17566 / 10
  | _ => 0

/-- Evaluating the certified upper and lower moment expressions proves the coefficient bounds. -/
theorem reflected_coeff_le_570 (j : ℕ) (hj : j ≤ 5) :
    reflectedCap570 j - 3 * reflectedFloor570 j ≤ reflectedCoeff570 j := by
  apply (sub_le_sub_right (cap_le j) _).trans
  interval_cases j <;>
    norm_num only [reflectedCoeff570, reflectedFloor570, capRat, momentFloor570,
      Analysis.logPowerTailPoly, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
      Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat, Nat.reduceSub, Nat.reduceAdd]

/-- The exponential monomial occurring after the kernel normalization is absorbed into the shift. -/
private noncomputable def scaled (k : ℕ) (z : ℝ) :=
  Real.exp (-(51 / 50 : ℝ) * z) * z ^ k

/-- Each scaled monomial of degree at most five decreases on the interval above fourteen. -/
private theorem scaled_anti (k : ℕ) (hk : k ≤ 5) : AntitoneOn (scaled k) (Set.Ici 14) := by
  have hd (z : ℝ) :=
    (((hasDerivAt_id z).const_mul (-(51 / 50 : ℝ))).exp).mul ((hasDerivAt_id z).pow k)
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact fun z _ ↦ (hd z).continuousAt.continuousWithinAt
  · exact fun z _ ↦ (hd z).differentiableAt.differentiableWithinAt
  · intro z hz
    have hz' : 14 ≤ z := interior_subset hz
    change deriv ((fun x : ℝ ↦ Real.exp (-(51 / 50 : ℝ) * id x)) * (id : ℝ → ℝ) ^ k) z ≤ 0
    rw [(hd z).deriv]
    simp only [id_eq, mul_one, Pi.pow_apply]
    cases k with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, pow_zero, mul_one]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by norm_num only)
    | succ k =>
      have hk' : ((k + 1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast hk
      have hn : ((k + 1 : ℕ) : ℝ) - 51 / 50 * z ≤ 0 := by linarith only [hk', hz']
      have hw : 0 ≤ Real.exp (-(51 / 50 : ℝ) * z) * z ^ k := by
        exact mul_nonneg (Real.exp_pos _).le (pow_nonneg (by linarith only [hz']) k)
      simp only [Nat.succ_sub_one, pow_succ]
      linear_combination mul_nonpos_of_nonneg_of_nonpos hw hn

/-- Enclose the shifted logarithm of radii from 278 through 285 using the endpoint logs. -/
private theorem z_bounds {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285) :
    140552 / 10000 ≤ 14 / 5 + 2 * Real.log r ∧ 14 / 5 + 2 * Real.log r ≤ 14105 / 1000 := by
  have h0 :=
    (Analysis.rationalLogIntervalCheck_sound (N := 278) (j := 8) (n := 24) (lo := 56276 / 10000)
        (hi := 6) (by decide +kernel)).1
  have h1 :=
    (Analysis.rationalLogIntervalCheck_sound (N := 285) (j := 8) (n := 24) (lo := 5) (hi :=
        56525 / 10000) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Nat.cast_ofNat] at h0 h1
  constructor
  · linarith only [h0, Real.log_le_log (by norm_num only) hl]
  · linarith only [h1, Real.log_le_log (by linarith only [hl]) hu]

/-- A logarithm certificate gives an upper bound for the exponential at the lower shift. -/
private theorem exp_upper : Real.exp (-(51 / 50 : ℝ) * (140552 / 10000)) ≤ 5941 / 10000000000 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 10000000000 / 5941) (j := 21) (n := 32) (lo :=
        14) (hi := 143363 / 10000) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  have hh : Real.log (10000000000 / 5941 : ℝ) ≤ 51 / 50 * (140552 / 10000) := by linarith only [h]
  have he := (Real.log_le_iff_le_exp (by norm_num only : 0 < (10000000000 / 5941 : ℝ))).mp hh
  rw [neg_mul, Real.exp_neg]
  exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num only)).mpr (by linarith only [he])

/-- A logarithm certificate gives a lower bound for the exponential at the upper shift. -/
private theorem exp_lower : 5646 / 10000000000 ≤ Real.exp (-(51 / 50 : ℝ) * (14105 / 1000)) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 10000000000 / 5646) (j := 21) (n := 32) (lo :=
        143871 / 10000) (hi := 15) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  have hh : 51 / 50 * (14105 / 1000) ≤ Real.log (10000000000 / 5646 : ℝ) := by linarith only [h]
  have he := (Real.le_log_iff_exp_le (by norm_num only : 0 < (10000000000 / 5646 : ℝ))).mp hh
  rw [neg_mul, Real.exp_neg]
  apply (le_inv_comm₀ (by norm_num only) (Real.exp_pos _)).mpr
  norm_num only
  linarith only [he]

/-- Monotonicity bounds each scaled monomial from below at the largest shift. -/
private theorem scaled_bounds {z : ℝ} (hl : 140552 / 10000 ≤ z) (hu : z ≤ 14105 / 1000) (k : ℕ)
    (hk : k ≤ 5) : 5646 / 10000000000 * (14105 / 1000) ^ k ≤ scaled k z := by
  apply
    le_trans _
      (scaled_anti k hk (show 14 ≤ z by linarith only [hl])
        (show (14 : ℝ) ≤ 14105 / 1000 by norm_num only) hu)
  exact mul_le_mul_of_nonneg_right exp_lower (by positivity)

/-- Use the upper shift for negative coefficients and the lower shift for the positive
constant term to prove the uniform signed polynomial estimate. -/
private theorem endpoint_poly {z : ℝ} (hl : 140552 / 10000 ≤ z) (hu : z ≤ 14105 / 1000) :
    (51 / 50 : ℝ) ^ 5 / 120 *
        (∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * scaled (5 - j) z * reflectedCoeff570 j) <
      -(273 / 10000) := by
  have h0 := scaled_bounds hl hu 5 (by decide)
  have h1 := scaled_bounds hl hu 4 (by decide)
  have h2 := scaled_bounds hl hu 3 (by decide)
  have h3 := scaled_bounds hl hu 2 (by decide)
  have h4 := scaled_bounds hl hu 1 (by decide)
  have h5 : scaled 0 z ≤ 5941 / 10000000000 := by
    have h :=
      scaled_anti 0 (by decide) (by norm_num only : (14 : ℝ) ≤ 140552 / 10000)
        (show 14 ≤ z by linarith only [hl]) hl
    exact h.trans (by simpa only [scaled, pow_zero, mul_one] using exp_upper)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, reflectedCoeff570]
  linarith only [h0, h1, h2, h3, h4, h5]

/-- The section 31 reflected sum with the shifted exponential normalization is strictly below
minus 0.0273 for radii from 278 through 285 under RH and the prefix sign hypotheses. -/
theorem reflected_negative_570 (hRH : RiemannHypothesis) {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285)
    (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    let z := 14 / 5 + 2 * Real.log r
    (51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * z) *
        (-(∑' n : ℕ, τ n * reflectedWeight570 z n)) <
      -(273 / 10000) := by
  intro z
  obtain ⟨ha, hb⟩ := z_bounds hl hu
  have hz : 0 ≤ z := by
    dsimp only [z]; linarith only [ha]
  have h := reflected_polynomial_570 hRH hz τ ht hp
  have hc :=
    Finset.sum_le_sum (s := Finset.range 6)
      (fun j hj ↦
        mul_le_mul_of_nonneg_left
          (reflected_coeff_le_570 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
          (mul_nonneg (Nat.cast_nonneg (Nat.choose 5 j)) (pow_nonneg hz (5 - j))))
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (h.trans hc) (by positivity))
  rw [mul_assoc, Finset.mul_sum]
  have hd (j : ℕ) :
    Real.exp (-(51 / 50 : ℝ) * z) * ((Nat.choose 5 j : ℝ) * z ^ (5 - j) * reflectedCoeff570 j) =
      (Nat.choose 5 j : ℝ) * scaled (5 - j) z * reflectedCoeff570 j := by
    unfold scaled; ring
  simp only [hd]
  exact endpoint_poly ha hb

/-- For radii from 278 through 285 the signed reflected Euler sum with the section 31
kernel prefactor is strictly below minus 0.0273 under RH and the prefix sign hypotheses. -/
theorem reflected_kernel_bound_570 (hRH : RiemannHypothesis) {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285)
    (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * (14 / 5))) * r ^ (-(2 * (51 / 50 : ℝ))) *
        (-(∑' n : ℕ, τ n * reflectedWeight570 (14 / 5 + 2 * Real.log r) n)) <
      -(273 / 10000) := by
  have h := reflected_negative_570 hRH hl hu τ ht hp
  dsimp only at h
  rw [Real.rpow_def_of_pos (by linarith only [hl] : 0 < r), mul_assoc _ (Real.exp _) (Real.exp _), ←
    Real.exp_add]
  convert h using 4
  ring

/-- Enclose the shifted logarithm of radii from 285 through 287 using the endpoint logs. -/
private theorem z_bounds_574 {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 287) :
    141048 / 10000 ≤ 14 / 5 + 2 * Real.log r ∧ 14 / 5 + 2 * Real.log r ≤ 14119 / 1000 := by
  have h0 :=
    (Analysis.rationalLogIntervalCheck_sound (N := 285) (j := 8) (n := 24) (lo := 56524 / 10000)
        (hi := 6) (by decide +kernel)).1
  have h1 :=
    (Analysis.rationalLogIntervalCheck_sound (N := 287) (j := 8) (n := 24) (lo := 5) (hi :=
        56595 / 10000) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Nat.cast_ofNat] at h0 h1
  constructor
  · linarith only [h0, Real.log_le_log (by norm_num only) hl]
  · linarith only [h1, Real.log_le_log (by linarith only [hl]) hu]

/-- A logarithm certificate gives an upper bound for the exponential at the lower shift. -/
private theorem exp_upper_574 :
    Real.exp (-(51 / 50 : ℝ) * (141048 / 10000)) ≤ 5648 / 10000000000 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 10000000000 / 5648) (j := 21) (n := 32) (lo :=
        14) (hi := 143868 / 10000) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  have hh : Real.log (10000000000 / 5648 : ℝ) ≤ 51 / 50 * (141048 / 10000) := by linarith only [h]
  have he := (Real.log_le_iff_le_exp (by norm_num only : 0 < (10000000000 / 5648 : ℝ))).mp hh
  rw [neg_mul, Real.exp_neg]
  exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num only)).mpr (by linarith only [he])

/-- A logarithm certificate gives a lower bound for the exponential at the upper shift. -/
private theorem exp_lower_574 :
    55662 / 100000000000 ≤ Real.exp (-(51 / 50 : ℝ) * (14119 / 1000)) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 100000000000 / 55662) (j := 21) (n := 32) (lo :=
        1440138 / 100000) (hi := 15) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  have hh : 51 / 50 * (14119 / 1000) ≤ Real.log (100000000000 / 55662 : ℝ) := by linarith only [h]
  have he := (Real.le_log_iff_exp_le (by norm_num only : 0 < (100000000000 / 55662 : ℝ))).mp hh
  rw [neg_mul, Real.exp_neg]
  apply (le_inv_comm₀ (by norm_num only) (Real.exp_pos _)).mpr
  norm_num only
  linarith only [he]

/-- Monotonicity bounds each scaled monomial from below at the largest shift. -/
private theorem scaled_bounds_574 {z : ℝ} (hl : 141048 / 10000 ≤ z) (hu : z ≤ 14119 / 1000) (k : ℕ)
    (hk : k ≤ 5) : 55662 / 100000000000 * (14119 / 1000) ^ k ≤ scaled k z := by
  apply
    le_trans _
      (scaled_anti k hk (show 14 ≤ z by linarith only [hl])
        (show (14 : ℝ) ≤ 14119 / 1000 by norm_num only) hu)
  exact mul_le_mul_of_nonneg_right exp_lower_574 (by positivity)

/-- Use the upper shift for negative coefficients and the lower shift for the positive
constant term to prove the uniform signed polynomial estimate. -/
private theorem endpoint_poly_574 {z : ℝ} (hl : 141048 / 10000 ≤ z) (hu : z ≤ 14119 / 1000) :
    (51 / 50 : ℝ) ^ 5 / 120 *
        (∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * scaled (5 - j) z * reflectedCoeff570 j) <
      -(2705 / 100000) := by
  have h0 := scaled_bounds_574 hl hu 5 (by decide)
  have h1 := scaled_bounds_574 hl hu 4 (by decide)
  have h2 := scaled_bounds_574 hl hu 3 (by decide)
  have h3 := scaled_bounds_574 hl hu 2 (by decide)
  have h4 := scaled_bounds_574 hl hu 1 (by decide)
  have h5 : scaled 0 z ≤ 5648 / 10000000000 := by
    have h :=
      scaled_anti 0 (by decide) (by norm_num only : (14 : ℝ) ≤ 141048 / 10000)
        (show 14 ≤ z by linarith only [hl]) hl
    exact h.trans (by simpa only [scaled, pow_zero, mul_one] using exp_upper_574)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, reflectedCoeff570]
  linarith only [h0, h1, h2, h3, h4, h5]

/-- The section 62 reflected sum with the shifted exponential normalization is strictly below
minus 0.02705 for radii from 285 through 287 under RH and the prefix sign hypotheses. -/
theorem reflected_negative_574 (hRH : RiemannHypothesis) {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 287)
    (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    let z := 14 / 5 + 2 * Real.log r
    (51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * z) *
        (-(∑' n : ℕ, τ n * reflectedWeight570 z n)) <
      -(2705 / 100000) := by
  intro z
  obtain ⟨ha, hb⟩ := z_bounds_574 hl hu
  have hz : 0 ≤ z := by
    dsimp only [z]; linarith only [ha]
  have h := reflected_polynomial_570 hRH hz τ ht hp
  have hc :=
    Finset.sum_le_sum (s := Finset.range 6)
      (fun j hj ↦
        mul_le_mul_of_nonneg_left
          (reflected_coeff_le_570 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
          (mul_nonneg (Nat.cast_nonneg (Nat.choose 5 j)) (pow_nonneg hz (5 - j))))
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (h.trans hc) (by positivity))
  rw [mul_assoc, Finset.mul_sum]
  have hd (j : ℕ) :
    Real.exp (-(51 / 50 : ℝ) * z) * ((Nat.choose 5 j : ℝ) * z ^ (5 - j) * reflectedCoeff570 j) =
      (Nat.choose 5 j : ℝ) * scaled (5 - j) z * reflectedCoeff570 j := by
    unfold scaled; ring
  simp only [hd]
  exact endpoint_poly_574 ha hb

/-- For radii from 285 through 287 the signed reflected Euler sum with the section 62
kernel prefactor is strictly below minus 0.02705 under RH and the prefix sign hypotheses. -/
theorem reflected_kernel_bound_574 (hRH : RiemannHypothesis) {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 287)
    (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * (14 / 5))) * r ^ (-(2 * (51 / 50 : ℝ))) *
        (-(∑' n : ℕ, τ n * reflectedWeight570 (14 / 5 + 2 * Real.log r) n)) <
      -(2705 / 100000) := by
  have h := reflected_negative_574 hRH hl hu τ ht hp
  dsimp only at h
  rw [Real.rpow_def_of_pos (by linarith only [hl] : 0 < r), mul_assoc _ (Real.exp _) (Real.exp _), ←
    Real.exp_add]
  convert h using 4
  ring

/-- Enclose the shifted logarithm of radii from 287 through 288 using the endpoint logs. -/
private theorem z_bounds_576 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) :
    1411896 / 100000 ≤ 14 / 5 + 2 * Real.log r ∧ 14 / 5 + 2 * Real.log r ≤ 1412594 / 100000 := by
  have h0 :=
    (Analysis.rationalLogIntervalCheck_sound (N := 287) (j := 8) (n := 24) (lo := 565948 / 100000)
        (hi := 6) (by decide +kernel)).1
  have h1 :=
    (Analysis.rationalLogIntervalCheck_sound (N := 288) (j := 8) (n := 24) (lo := 5) (hi :=
        566297 / 100000) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Nat.cast_ofNat] at h0 h1
  constructor
  · linarith only [h0, Real.log_le_log (by norm_num only) hl]
  · linarith only [h1, Real.log_le_log (by linarith only [hl]) hu]

/-- A logarithm certificate gives an upper bound for the exponential at the lower shift. -/
private theorem exp_upper_576 :
    Real.exp (-(51 / 50 : ℝ) * (1411896 / 100000)) ≤ 5567 / 10000000000 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 10000000000 / 5567) (j := 21) (n := 32) (lo :=
        14) (hi := 1440133 / 100000) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  have hh : Real.log (10000000000 / 5567 : ℝ) ≤ 51 / 50 * (1411896 / 100000) := by linarith only [h]
  have he := (Real.log_le_iff_le_exp (by norm_num only : 0 < (10000000000 / 5567 : ℝ))).mp hh
  rw [neg_mul, Real.exp_neg]
  exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num only)).mpr (by linarith only [he])

/-- A logarithm certificate gives a lower bound for the exponential at the upper shift. -/
private theorem exp_lower_576 :
    55269 / 100000000000 ≤ Real.exp (-(51 / 50 : ℝ) * (1412594 / 100000)) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 100000000000 / 55269) (j := 21) (n := 32) (lo :=
        144084588 / 10000000) (hi := 15) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  have hh : 51 / 50 * (1412594 / 100000) ≤ Real.log (100000000000 / 55269 : ℝ) := by
    linarith only [h]
  have he := (Real.le_log_iff_exp_le (by norm_num only : 0 < (100000000000 / 55269 : ℝ))).mp hh
  rw [neg_mul, Real.exp_neg]
  apply (le_inv_comm₀ (by norm_num only) (Real.exp_pos _)).mpr
  norm_num only
  linarith only [he]

/-- Monotonicity bounds each scaled monomial from below at the largest shift. -/
private theorem scaled_bounds_576 {z : ℝ} (hl : 1411896 / 100000 ≤ z) (hu : z ≤ 1412594 / 100000)
    (k : ℕ) (hk : k ≤ 5) : 55269 / 100000000000 * (1412594 / 100000) ^ k ≤ scaled k z := by
  apply
    le_trans _
      (scaled_anti k hk (show 14 ≤ z by linarith only [hl])
        (show (14 : ℝ) ≤ 1412594 / 100000 by norm_num only) hu)
  exact mul_le_mul_of_nonneg_right exp_lower_576 (by positivity)

/-- Use the upper shift for negative coefficients and the lower shift for the positive
constant term to prove the uniform signed polynomial estimate. -/
private theorem endpoint_poly_576 {z : ℝ} (hl : 1411896 / 100000 ≤ z) (hu : z ≤ 1412594 / 100000) :
    (51 / 50 : ℝ) ^ 5 / 120 *
        (∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * scaled (5 - j) z * reflectedCoeff570 j) <
      -(2691 / 100000) := by
  have h0 := scaled_bounds_576 hl hu 5 (by decide)
  have h1 := scaled_bounds_576 hl hu 4 (by decide)
  have h2 := scaled_bounds_576 hl hu 3 (by decide)
  have h3 := scaled_bounds_576 hl hu 2 (by decide)
  have h4 := scaled_bounds_576 hl hu 1 (by decide)
  have h5 : scaled 0 z ≤ 5567 / 10000000000 := by
    have h :=
      scaled_anti 0 (by decide) (by norm_num only : (14 : ℝ) ≤ 1411896 / 100000)
        (show 14 ≤ z by linarith only [hl]) hl
    exact h.trans (by simpa only [scaled, pow_zero, mul_one] using exp_upper_576)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, reflectedCoeff570]
  linarith only [h0, h1, h2, h3, h4, h5]

/-- The section 86 reflected sum with the shifted exponential normalization is strictly below
minus 0.02691 for radii from 287 through 288 under RH and the prefix sign hypotheses. -/
theorem reflected_negative_576 (hRH : RiemannHypothesis) {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288)
    (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    let z := 14 / 5 + 2 * Real.log r
    (51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * z) *
        (-(∑' n : ℕ, τ n * reflectedWeight570 z n)) <
      -(2691 / 100000) := by
  intro z
  obtain ⟨ha, hb⟩ := z_bounds_576 hl hu
  have hz : 0 ≤ z := by
    dsimp only [z]; linarith only [ha]
  have h := reflected_polynomial_570 hRH hz τ ht hp
  have hc :=
    Finset.sum_le_sum (s := Finset.range 6)
      (fun j hj ↦
        mul_le_mul_of_nonneg_left
          (reflected_coeff_le_570 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
          (mul_nonneg (Nat.cast_nonneg (Nat.choose 5 j)) (pow_nonneg hz (5 - j))))
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (h.trans hc) (by positivity))
  rw [mul_assoc, Finset.mul_sum]
  have hd (j : ℕ) :
    Real.exp (-(51 / 50 : ℝ) * z) * ((Nat.choose 5 j : ℝ) * z ^ (5 - j) * reflectedCoeff570 j) =
      (Nat.choose 5 j : ℝ) * scaled (5 - j) z * reflectedCoeff570 j := by
    unfold scaled; ring
  simp only [hd]
  exact endpoint_poly_576 ha hb

/-- For radii from 287 through 288 the signed reflected Euler sum with the section 86
kernel prefactor is strictly below minus 0.02691 under RH and the prefix sign hypotheses. -/
theorem reflected_kernel_bound_576 (hRH : RiemannHypothesis) {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288)
    (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * (14 / 5))) * r ^ (-(2 * (51 / 50 : ℝ))) *
        (-(∑' n : ℕ, τ n * reflectedWeight570 (14 / 5 + 2 * Real.log r) n)) <
      -(2691 / 100000) := by
  have h := reflected_negative_576 hRH hl hu τ ht hp
  dsimp only at h
  rw [Real.rpow_def_of_pos (by linarith only [hl] : 0 < r), mul_assoc _ (Real.exp _) (Real.exp _), ←
    Real.exp_add]
  convert h using 4
  ring

/-- Up to radius 292 the signed reflected sum saves more than 0.02.
Bound the polynomial at shift 14 and the exponential at the largest shift. -/
theorem reflected_negative_584 (hRH : RiemannHypothesis) {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 292)
    (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    let z := 14 / 5 + 2 * Real.log r
    (51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * z) *
        (-(∑' n : ℕ, τ n * reflectedWeight570 z n)) <
      -(2 / 100) := by
  intro z
  have ha := (z_bounds_576 (le_refl (287 : ℝ)) (by norm_num only)).1
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 24) (lo := 5) (hi :=
        568 / 100) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hz : 14 ≤ z := by
    dsimp only [z]
    linarith only [ha, Real.log_le_log (by norm_num only) hl]
  have hzu : z ≤ 1416 / 100 := by
    dsimp only [z]
    linarith only [hlog, Real.log_le_log (by linarith only [hl]) hu]
  have hz0 : 0 ≤ z := by linarith only [hz]
  have h := reflected_polynomial_570 hRH hz0 τ ht hp
  have hc :=
    Finset.sum_le_sum (s := Finset.range 6)
      (fun j hj ↦
        mul_le_mul_of_nonneg_left
          (reflected_coeff_le_570 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
          (mul_nonneg (Nat.cast_nonneg (Nat.choose 5 j)) (pow_nonneg hz0 (5 - j))))
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (h.trans hc) (by positivity))
  have hp (k : ℕ) := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 14) hz k
  have hpoly :
    (∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * z ^ (5 - j) * reflectedCoeff570 j) ≤
      -4500000 := by
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
      Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, reflectedCoeff570, pow_zero]
    linarith only [hp 1, hp 2, hp 3, hp 4, hp 5]
  have he :=
    (Analysis.rationalLogIntervalCheck_sound (N := 2000000) (j := 21) (n := 32) (lo := 145 / 10)
        (hi := 15) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at he
  have hex :=
    (Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 2000000)).mp
      (show 51 / 50 * z ≤ Real.log 2000000 by linarith only [he, hzu])
  have hi := one_div_le_one_div_of_le (Real.exp_pos _) hex
  rw [one_div (Real.exp _), ← Real.exp_neg, ← neg_mul] at hi
  have hc' :=
    mul_le_mul_of_nonneg_left hpoly
      (show 0 ≤ (51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * z) by positivity)
  linarith only [hc', hi]

/-- For radii from 287 through 292 the signed reflected Euler sum with the section 86
kernel prefactor is strictly below minus 0.02 under RH and the prefix sign hypotheses. -/
theorem reflected_kernel_bound_584 (hRH : RiemannHypothesis) {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 292)
    (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * (14 / 5))) * r ^ (-(2 * (51 / 50 : ℝ))) *
        (-(∑' n : ℕ, τ n * reflectedWeight570 (14 / 5 + 2 * Real.log r) n)) <
      -(2 / 100) := by
  have h := reflected_negative_584 hRH hl hu τ ht hp
  dsimp only at h
  rw [Real.rpow_def_of_pos (by linarith only [hl] : 0 < r), mul_assoc _ (Real.exp _) (Real.exp _), ←
    Real.exp_add]
  convert h using 4
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
