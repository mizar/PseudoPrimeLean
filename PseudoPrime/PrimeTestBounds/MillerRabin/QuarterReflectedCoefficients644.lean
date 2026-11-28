/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedCap644
import all PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3
import all PseudoPrime.Analysis.LogTaylorBounds

/-! # Rational upper bounds for the six section 122 reflected coefficients -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Outward rational upper bounds for the six signed reflected coefficients. -/
def reflectedCoeff644 : ℕ → ℝ
  | 0 => -3.727311
  | 1 => -8.055258
  | 2 => -24.686311
  | 3 => -92.428970
  | 4 => -345.337733
  | 5 => -462.750289
  | _ => 0

private theorem moment_upper {d t p z : ℝ} (hd : 0 < d) (ht : 1 ≤ t) (hp : t ^ (-d) ≤ p)
    (hz : Real.log t ≤ z) (j : ℕ) :
    eulerMomentValue570 d j t ≤ p * Analysis.logPowerTailPoly d j z := by
  have hl := Real.log_nonneg ht
  exact
    mul_le_mul hp (Analysis.log_power_tail_poly_mono hd hl hz j)
      (Analysis.log_power_tail_poly_nonneg hd hl j)
      ((Real.rpow_nonneg (zero_le_one.trans ht) _).trans hp)

private theorem log_million : Real.log 1000000 ≤ (13.816 : ℝ) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 10) (j := 3) (n := 16) (lo := 0) (hi :=
        23026 / 10000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  rw [show (1000000 : ℝ) = 10 ^ 6 by norm_num only, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h]

private theorem cap_upper (j : ℕ) :
    reflectedCap644 j ≤
      0.01106702744662 * Analysis.logPowerTailPoly (57 / 100) j 7.901377357 +
        (4 / 5) * (0.00021294561180 * (7.901377357 : ℝ) ^ j) +
        (4 / 5 * (157 / 100)) *
          (0.00021294561180 * Analysis.logPowerTailPoly (107 / 100) j 7.901377357) +
        (157 / 100 / 24) *
          (0.0000003802 * Analysis.logPowerTailPoly (107 / 100) (j + 2) 13.816) := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 2701) (j := 12) (n := 27) (lo :=
        7901377350 / 1000000000) (hi := 7901377357 / 1000000000) (by decide +kernel)).2
  have hd :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 2701) (p := 57) (d :=
        100) (lo := 0) (hi := 1106702744662 / 100000000000000) (by decide +kernel)).2
  have ha :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 2701) (p := 107) (d :=
        100) (lo := 0) (hi := 21294561180 / 100000000000000) (by decide +kernel)).2
  have hU :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1000000) (p := 107)
        (d := 100) (lo := 0) (hi := 3802 / 10000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hl hd ha hU
  have hm := moment_upper (by norm_num only : (0 : ℝ) < 57 / 100) (by norm_num only) hd hl j
  have he := moment_upper (by norm_num only : (0 : ℝ) < 107 / 100) (by norm_num only) ha hl j
  have hh :=
    moment_upper (by norm_num only : (0 : ℝ) < 107 / 100) (by norm_num only) hU log_million (j + 2)
  have hLog : 0 ≤ Real.log (2701 : ℝ) := Real.log_nonneg (by norm_num only)
  have hb :
    Real.sqrt 2701 * eulerMoment570 (57 / 100) j 2701 ≤
      (1064728059 / 5000000000000 : ℝ) * (7901377357 / 1000000000 : ℝ) ^ j := by
    unfold eulerMoment570
    rw [mul_left_comm, Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num only : (0 : ℝ) < 2701),
      show (1 / 2 : ℝ) + (-(57 / 100) - 1) = -(107 / 100) by norm_num only, mul_comm]
    exact
      mul_le_mul ha (pow_le_pow_left₀ hLog hl j) (pow_nonneg hLog _)
        ((Real.rpow_nonneg (by norm_num only) _).trans ha)
  unfold reflectedCap644 reflectedCapFrom644
  linarith only [hm, he, hh, hb]

/-- Rational upper bounds for the six shifted reflected moments above 99000. -/
theorem reflected_shift_cap_upper_644 (j : ℕ) :
    reflectedCapFrom644 99000 j ≤
      0.001420653 * Analysis.logPowerTailPoly (57 / 100) j 11.502876 +
        (4 / 5) * (0.000004515131 * (11.502876 : ℝ) ^ j) +
        (4 / 5 * (157 / 100)) *
          (0.000004515131 * Analysis.logPowerTailPoly (107 / 100) j 11.502876) +
        (157 / 100 / 24) *
          (0.0000003802 * Analysis.logPowerTailPoly (107 / 100) (j + 2) 13.816) := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 99000) (j := 16) (n := 27) (lo := 11) (hi :=
        11502876 / 1000000) (by decide +kernel)).2
  have hd :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 99000) (p := 57) (d :=
        100) (lo := 0) (hi := 1420653 / 1000000000) (by decide +kernel)).2
  have ha :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 99000) (p := 107) (d :=
        100) (lo := 0) (hi := 4515131 / 1000000000000) (by decide +kernel)).2
  have hU :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1000000) (p := 107)
        (d := 100) (lo := 0) (hi := 3802 / 10000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hl hd ha hU
  have hm := moment_upper (by norm_num only : (0 : ℝ) < 57 / 100) (by norm_num only) hd hl j
  have he := moment_upper (by norm_num only : (0 : ℝ) < 107 / 100) (by norm_num only) ha hl j
  have hh :=
    moment_upper (by norm_num only : (0 : ℝ) < 107 / 100) (by norm_num only) hU log_million (j + 2)
  have hLog : 0 ≤ Real.log (99000 : ℝ) := Real.log_nonneg (by norm_num only)
  have hb :
    Real.sqrt 99000 * eulerMoment570 (57 / 100) j 99000 ≤
      (4515131 / 1000000000000 : ℝ) * (2875719 / 250000 : ℝ) ^ j := by
    unfold eulerMoment570
    rw [mul_left_comm, Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num only : (0 : ℝ) < 99000),
      show (1 / 2 : ℝ) + (-(57 / 100) - 1) = -(107 / 100) by norm_num only, mul_comm]
    exact
      mul_le_mul ha (pow_le_pow_left₀ hLog hl j) (pow_nonneg hLog _)
        ((Real.rpow_nonneg (by norm_num only) _).trans ha)
  unfold reflectedCapFrom644
  linarith only [hm, he, hh, hb]

/-- Each signed coefficient in the reflected polynomial is bounded above
by its outward rational value, using only two distinct moment endpoints. -/
theorem reflected_coeff_upper_644 (j : ℕ) (hj : j ≤ 5) :
    reflectedCap644 j - 3 * reflectedFloor644 j ≤ reflectedCoeff644 j := by
  have h := cap_upper j
  interval_cases j <;>
    norm_num only [reflectedCoeff644, reflectedFloor644, momentFloor570, Analysis.logPowerTailPoly,
      Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat, Nat.cast_one,
      Nat.cast_zero, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] at h ⊢ <;>
    linarith only [h]

/-- All six outward rational coefficients are strictly negative. -/
theorem reflected_coeff_neg_644 (j : ℕ) (hj : j ≤ 5) : reflectedCoeff644 j < 0 := by
  interval_cases j <;> norm_num only [reflectedCoeff644]

private theorem shift_pos {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    0 < (2687 / 1000 : ℝ) + 2 * Real.log r := by
  linarith only [Real.log_nonneg (show 1 ≤ r by linarith only [hr.1])]

private theorem radius_factor_antitone {k : ℕ} (hk : k ≤ 5) :
    AntitoneOn (fun r : ℝ ↦ r ^ (-(107 / 50) : ℝ) * (2687 / 1000 + 2 * Real.log r) ^ k)
      (Set.Icc 316 322) := by
  intro r hr u hu hru
  let z := fun x : ℝ ↦ 2687 / 1000 + 2 * Real.log x
  have he (t : ℝ) (ht : t ∈ Set.Icc 316 322) :
    t ^ (-(107 / 50) : ℝ) * z t ^ k = quarterRecoveryFactor (2687 / 1000) t / z t ^ (5 - k) := by
    apply (eq_div_iff (pow_pos (shift_pos ht) _).ne').mpr
    unfold quarterRecoveryFactor
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hk]
  change u ^ (-(107 / 50) : ℝ) * z u ^ k ≤ r ^ (-(107 / 50) : ℝ) * z r ^ k
  rw [he u hu, he r hr]
  have hp : 0 < r := by linarith only [hr.1]
  have hz : z r ≤ z u := by
    dsimp only [z]
    linarith only [Real.log_le_log hp hru]
  apply div_le_div₀
  · exact mul_nonneg (Real.rpow_nonneg hp.le _) (pow_nonneg (shift_pos hr).le _)
  · exact quarter_recovery_factor_antitone (by norm_num only) hr hu hru
  · exact pow_pos (shift_pos hr) _
  · exact pow_le_pow_left₀ (shift_pos hr).le hz _

/-- The certified reflected polynomial with its common Mellin normalization.
Its six coefficients are negative, so the expression grows with the radius. -/
noncomputable def reflectedEnvelope644 (r : ℝ) : ℝ :=
  ((107 / 100 : ℝ) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120) *
    ∑ j ∈ Finset.range 6,
      (Nat.choose 5 j : ℝ) * (r ^ (-(107 / 50) : ℝ) * (2687 / 1000 + 2 * Real.log r) ^ (5 - j)) *
        reflectedCoeff644 j

/-- The reflected envelope is nondecreasing on the entire section 122
radius range. Each negative coefficient reverses the radius-factor inequality. -/
theorem reflected_envelope_mono_644 : MonotoneOn reflectedEnvelope644 (Set.Icc 316 322) := by
  intro r hr u hu hru
  unfold reflectedEnvelope644
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j hj
  have h := radius_factor_antitone (k := 5 - j) (Nat.sub_le _ _) hr hu hru
  exact
    mul_le_mul_of_nonpos_right (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))
      (reflected_coeff_neg_644 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).le

/-- For any right endpoint inside the section 122 radius range, the signed
reflected series is bounded by the certified polynomial at that endpoint
minus the extra recovery. This is the form used in the four-row comparison. -/
theorem quarter_reflected_endpoint_644 (hRH : RiemannHypothesis) {r u : ℝ}
    (hr : r ∈ Set.Icc 316 322) (hu : u ∈ Set.Icc 316 322) (hru : r ≤ u) (τ : ℕ → ℝ)
    (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 99000, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    let z := 2687 / 1000 + 2 * Real.log r
    let D :=
      (107 / 100 : ℝ) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120 * r ^ (-(107 / 50) : ℝ)
    0 - D * (∑' n, τ n * (ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n)) ≤
      reflectedEnvelope644 u - 0.0013281 := by
  intro z D
  apply (quarter_reflected_upper_644 hRH hr τ ht hp).trans
  apply sub_le_sub_right _ _
  apply le_trans _ (reflected_envelope_mono_644 hr hu hru)
  unfold reflectedEnvelope644
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have h := reflected_coeff_upper_644 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  have hf : 0 ≤ r ^ (-(107 / 50) : ℝ) * ((Nat.choose 5 j : ℝ) * z ^ (5 - j)) :=
    mul_nonneg (Real.rpow_nonneg (by linarith only [hr.1]) _)
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (shift_pos hr).le _))
  have hm := mul_le_mul_of_nonneg_left h hf
  dsimp only [z] at hm
  linarith only [hm]

private theorem envelope_box {r p z : ℝ} (hp : 0 ≤ p) (hr : p ≤ r ^ (-(107 / 50) : ℝ)) (hz : 0 ≤ z)
    (hzr : z ≤ 2687 / 1000 + 2 * Real.log r) :
    reflectedEnvelope644 r ≤
      ((107 / 100 : ℝ) ^ 5 * (5641106227 / 100000000000) / 120) *
        (∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * (p * z ^ (5 - j)) * reflectedCoeff644 j) := by
  have hex :=
    Analysis.exp_le_taylor_add_two_next (x := (287509 / 100000 : ℝ)) (n := 24) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at hex
  have hl := one_div_le_one_div_of_le (Real.exp_pos _) hex
  rw [one_div (Real.exp _), ← Real.exp_neg] at hl
  have hE : (5641106227 / 100000000000 : ℝ) ≤ Real.exp (-(107 / 100) * (2687 / 1000)) := by
    rw [show -(107 / 100 : ℝ) * (2687 / 1000) = -(287509 / 100000) by norm_num only]
    linarith only [hl]
  have hs :
    (∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * (p * z ^ (5 - j)) * reflectedCoeff644 j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    exact
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hp (pow_nonneg hz _)))
        (reflected_coeff_neg_644 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).le
  have hC :
    ((107 / 100 : ℝ) ^ 5 * (5641106227 / 100000000000) / 120) ≤
      ((107 / 100 : ℝ) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120) := by
    linarith only [hE]
  unfold reflectedEnvelope644
  refine le_trans ?_ (mul_le_mul_of_nonpos_right hC hs)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro j hj
    have h := mul_le_mul hr (pow_le_pow_left₀ hz hzr (5 - j)) (pow_nonneg hz _) (hp.trans hr)
    exact
      mul_le_mul_of_nonpos_right (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))
        (reflected_coeff_neg_644 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).le

/-- The certified section 122 reflected polynomial at radius 320. -/
theorem reflected_envelope_644_320 : reflectedEnvelope644 (320) ≤ -0.01361249 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 320) (j := 9) (n := 27) (lo :=
        5768320987 / 1000000000) (hi := 5768321003 / 1000000000) (by decide +kernel)).1
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 320) (p := 107) (d :=
        50) (lo := 4354908618 / 1000000000000000) (hi := 4354908619 / 1000000000000000)
        (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hl hp
  have hb :=
    envelope_box (by norm_num only) hp (show (0 : ℝ) ≤ 14223641974 / 1000000000 by norm_num only)
      (by linarith only [hl])
  norm_num only [reflectedCoeff644, Nat.choose, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at hb
  linarith only [hb]

/-- The certified section 122 reflected polynomial at radius 1287 / 4. -/
theorem reflected_envelope_644_32175 : reflectedEnvelope644 (1287 / 4) ≤ -0.013498 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1287 / 4) (j := 9) (n := 27) (lo :=
        5773774838 / 1000000000) (hi := 5773774854 / 1000000000) (by decide +kernel)).1
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1287 / 4) (p := 107)
        (d := 50) (lo := 4304376890 / 1000000000000000) (hi := 4304376891 / 1000000000000000)
        (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hl hp
  have hb :=
    envelope_box (by norm_num only) hp (show (0 : ℝ) ≤ 14234549676 / 1000000000 by norm_num only)
      (by linarith only [hl])
  norm_num only [reflectedCoeff644, Nat.choose, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at hb
  linarith only [hb]

/-- The certified section 122 reflected polynomial at radius 1609 / 5. -/
theorem reflected_envelope_644_3218 : reflectedEnvelope644 (1609 / 5) ≤ -0.0134948 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1609 / 5) (j := 9) (n := 27) (lo :=
        5773930226 / 1000000000) (hi := 5773930242 / 1000000000) (by decide +kernel)).1
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1609 / 5) (p := 107)
        (d := 50) (lo := 4302945791 / 1000000000000000) (hi := 4302945792 / 1000000000000000)
        (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hl hp
  have hb :=
    envelope_box (by norm_num only) hp (show (0 : ℝ) ≤ 14234860452 / 1000000000 by norm_num only)
      (by linarith only [hl])
  norm_num only [reflectedCoeff644, Nat.choose, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at hb
  linarith only [hb]

/-- The certified section 122 reflected polynomial at radius 322. -/
theorem reflected_envelope_644_322 : reflectedEnvelope644 (322) ≤ -0.0134818 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 322) (j := 9) (n := 27) (lo :=
        5774551537 / 1000000000) (hi := 5774551553 / 1000000000) (by decide +kernel)).1
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 322) (p := 107) (d :=
        50) (lo := 4297228373 / 1000000000000000) (hi := 4297228374 / 1000000000000000)
        (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hl hp
  have hb :=
    envelope_box (by norm_num only) hp (show (0 : ℝ) ≤ 14236103074 / 1000000000 by norm_num only)
      (by linarith only [hl])
  norm_num only [reflectedCoeff644, Nat.choose, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at hb
  linarith only [hb]

end PseudoPrime.PrimeTestBounds.MillerRabin
