/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterConductor644
import all PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3
import all PseudoPrime.Analysis.LogTaylorBounds

/-! # Certified conductor and Euler endpoint values in section 122 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem momentUpper {d x p z : ℝ} (k : ℕ) (hd : 0 < d) (hx : 1 ≤ x) (hp : x ^ (-d) ≤ p)
    (hz : Real.log x ≤ z) : eulerMomentValue570 d k x ≤ p * Analysis.logPowerTailPoly d k z := by
  exact
    mul_le_mul hp (Analysis.log_power_tail_poly_mono hd (Real.log_nonneg hx) hz k)
      (Analysis.log_power_tail_poly_nonneg hd (Real.log_nonneg hx) k)
      ((Real.rpow_nonneg (zero_le_one.trans hx) _).trans hp)

/-- The logarithm of ten bounds the RH error polynomial at one million. -/
theorem euler_high_error_644 : eulerHighError644 1000000 ≤ 179 / 1000000 := by
  have hp : (1000000 : ℝ) ^ (-(107 / 100 : ℝ)) ≤ 3802 / 10000000000 := by
    have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1000000) (p := 107)
          (d := 100) (lo := 0) (hi := 3802 / 10000000000) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    linarith only [h]
  have hz : Real.log 1000000 ≤ 13816 / 1000 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 10) (j := 3) (n := 16) (lo := 0) (hi :=
          23026 / 10000) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] at h
    rw [show (1000000 : ℝ) = 10 ^ 6 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [h]
  have h0 :=
    momentUpper 2 (by norm_num only : (0 : ℝ) < 107 / 100) (by norm_num only : (1 : ℝ) ≤ 1000000) hp
      hz
  have h1 :=
    momentUpper 3 (by norm_num only : (0 : ℝ) < 107 / 100) (by norm_num only : (1 : ℝ) ≤ 1000000) hp
      hz
  have h2 :=
    momentUpper 4 (by norm_num only : (0 : ℝ) < 107 / 100) (by norm_num only : (1 : ℝ) ≤ 1000000) hp
      hz
  unfold eulerHighError644
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    Nat.reduceAdd] at h0 h1 h2
  linarith only [h0, h1, h2]

private theorem conductor_box {r z y : ℝ} (hr : 1 ≤ r) (hz : Real.log r ≤ z)
    (hy : r ^ (-(57 / 50) : ℝ) ≤ y) :
    quarterConductor644 r ≤
      (4 * (107 / 100) ^ 5 * (56411062281 / 1000000000000) / 120) *
        (y * (2687 / 1000 + 2 * z) ^ 5) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 287509 / 100000) 26
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at h
  have hi := one_div_le_one_div_of_le (by norm_num only) h
  rw [one_div (Real.exp _), ← Real.exp_neg] at hi
  have he : Real.exp (-(107 / 100 : ℝ) * (2687 / 1000)) ≤ 56411062281 / 1000000000000 := by
    rw [show -(107 / 100 : ℝ) * (2687 / 1000) = -(287509 / 100000) by norm_num only]
    linarith only [hi]
  have hl := Real.log_nonneg hr
  have hp := Real.rpow_nonneg (zero_le_one.trans hr) (-(57 / 50) : ℝ)
  have _hy := hp.trans hy
  unfold quarterConductor644
  gcongr

private theorem tail_box {x z m e : ℝ} (hx : 1 ≤ x) (hz : Real.log x ≤ z)
    (hm : x ^ (-(57 / 100) : ℝ) ≤ m) (he : x ^ (-(107 / 100) : ℝ) ≤ e) :
    positiveTail644 x ≤
      3 / 8 * (m * Analysis.logPowerTailPoly (57 / 100) 0 z) +
        321 / 800 * (m * Analysis.logPowerTailPoly (57 / 100) 1 z) +
        11449 / 80000 * (m * Analysis.logPowerTailPoly (57 / 100) 2 z) +
        4 / 5 * (e * (3 / 8 + 321 / 800 * z + 11449 / 80000 * z ^ 2)) +
        (3 / 20 * (e * Analysis.logPowerTailPoly (107 / 100) 0 z) +
          27499 / 100000 * (e * Analysis.logPowerTailPoly (107 / 100) 1 z) +
          1797493 / 10000000 * (e * Analysis.logPowerTailPoly (107 / 100) 2 z)) +
        179 / 1000000 := by
  have hlog := Real.log_nonneg hx
  have hx0 := zero_le_one.trans hx
  have he0 := (Real.rpow_nonneg hx0 _).trans he
  have hD :
    Real.sqrt x * eulerDensity644 x ≤ e * (3 / 8 + 321 / 800 * z + 11449 / 80000 * z ^ 2) := by
    unfold eulerDensity644
    rw [Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add (zero_lt_one.trans_le hx),
      show (1 / 2 : ℝ) + -(157 / 100) = -(107 / 100) by norm_num only]
    gcongr
  unfold positiveTail644 eulerMainTail644 eulerLowError644
  rw [mul_assoc]
  gcongr
  all_goals
    first
    | exact euler_high_error_644
    | exact momentUpper _ (by norm_num only) hx hm hz
    | exact momentUpper _ (by norm_num only) hx he hz

private theorem conductor_at_square {r z m : ℝ} (hr : 1 ≤ r) (hz : Real.log (r ^ 2) ≤ z)
    (hm : (r ^ 2) ^ (-(57 / 100) : ℝ) ≤ m) :
    quarterConductor644 r ≤
      (4 * (107 / 100) ^ 5 * (56411062281 / 1000000000000) / 120) *
        (m * (2687 / 1000 + z) ^ 5) := by
  rw [Real.log_pow, Nat.cast_ofNat] at hz
  rw [← Real.rpow_natCast_mul (zero_le_one.trans hr)] at hm
  norm_num only [Nat.cast_ofNat] at hm
  have h := conductor_box hr (show Real.log r ≤ z / 2 by linarith only [hz]) hm
  convert h using 1
  ring

/-- Certify the section 122 conductor and Euler loss at radius 316. -/
theorem quarter_euler_644_316 :
    quarterConductor644 (316) + 4 * positiveTail644 ((316) ^ 2) ≤ 2.463779 := by
  have hz :=
    (Analysis.rationalLogIntervalCheck_sound (N := 99856) (j := 17) (n := 22) (lo := 11) (hi :=
        115114844473 / 10000000000) (by decide +kernel)).2
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 99856) (p := 57) (d :=
        100) (lo := 0) (hi := 141369826767 / 100000000000000) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 99856) (p := 107) (d :=
        100) (lo := 0) (hi := 4473728697 / 1000000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hz hm he
  rw [show (99856 : ℝ) = (316) ^ 2 by norm_num only] at hz hm he
  have ht := tail_box (by norm_num only) hz hm he
  have hc := conductor_at_square (by norm_num only) hz hm
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    Nat.reduceAdd] at ht hc
  linarith only [ht, hc]

/-- Certify the section 122 conductor and Euler loss at radius 320. -/
theorem quarter_euler_644_320 :
    quarterConductor644 (320) + 4 * positiveTail644 ((320) ^ 2) ≤ 2.448593 := by
  have hz :=
    (Analysis.rationalLogIntervalCheck_sound (N := 102400) (j := 17) (n := 22) (lo := 11) (hi :=
        115366420117 / 10000000000) (by decide +kernel)).2
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 102400) (p := 57) (d :=
        100) (lo := 0) (hi := 139357075794 / 100000000000000) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 102400) (p := 107) (d :=
        100) (lo := 0) (hi := 4354908620 / 1000000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hz hm he
  rw [show (102400 : ℝ) = (320) ^ 2 by norm_num only] at hz hm he
  have ht := tail_box (by norm_num only) hz hm he
  have hc := conductor_at_square (by norm_num only) hz hm
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    Nat.reduceAdd] at ht hc
  linarith only [ht, hc]

/-- Certify the section 122 conductor and Euler loss at radius 1287 / 4. -/
theorem quarter_euler_644_32175 :
    quarterConductor644 (1287 / 4) + 4 * positiveTail644 ((1287 / 4) ^ 2) ≤ 2.442030 := by
  have hz :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1656369 / 16) (j := 17) (n := 22) (lo := 11)
        (hi := 115475497131 / 10000000000) (by decide +kernel)).2
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1656369 / 16) (p := 57)
        (d := 100) (lo := 0) (hi := 138493326451 / 100000000000000) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1656369 / 16) (p := 107)
        (d := 100) (lo := 0) (hi := 4304376892 / 1000000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hz hm he
  rw [show (1656369 / 16 : ℝ) = (1287 / 4) ^ 2 by norm_num only] at hz hm he
  have ht := tail_box (by norm_num only) hz hm he
  have hc := conductor_at_square (by norm_num only) hz hm
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    Nat.reduceAdd] at ht hc
  linarith only [ht, hc]

/-- Certify the section 122 conductor and Euler loss at radius 1609 / 5. -/
theorem quarter_euler_644_3218 :
    quarterConductor644 (1609 / 5) + 4 * positiveTail644 ((1609 / 5) ^ 2) ≤ 2.441843 := by
  have hz :=
    (Analysis.rationalLogIntervalCheck_sound (N := 2588881 / 25) (j := 17) (n := 22) (lo := 11)
        (hi := 115478604893 / 10000000000) (by decide +kernel)).2
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 2588881 / 25) (p := 57)
        (d := 100) (lo := 0) (hi := 138468795582 / 100000000000000) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 2588881 / 25) (p := 107)
        (d := 100) (lo := 0) (hi := 4302945793 / 1000000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hz hm he
  rw [show (2588881 / 25 : ℝ) = (1609 / 5) ^ 2 by norm_num only] at hz hm he
  have ht := tail_box (by norm_num only) hz hm he
  have hc := conductor_at_square (by norm_num only) hz hm
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    Nat.reduceAdd] at ht hc
  linarith only [ht, hc]

/-- Certify the section 122 conductor and Euler loss at radius 322. -/
theorem quarter_euler_644_322 :
    quarterConductor644 (322) + 4 * positiveTail644 ((322) ^ 2) ≤ 2.441096 := by
  have hz :=
    (Analysis.rationalLogIntervalCheck_sound (N := 103684) (j := 17) (n := 22) (lo := 11) (hi :=
        115491031112 / 10000000000) (by decide +kernel)).2
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 103684) (p := 57) (d :=
        100) (lo := 0) (hi := 138370753618 / 100000000000000) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 103684) (p := 107) (d :=
        100) (lo := 0) (hi := 4297228375 / 1000000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hz hm he
  rw [show (103684 : ℝ) = (322) ^ 2 by norm_num only] at hz hm he
  have ht := tail_box (by norm_num only) hz hm he
  have hc := conductor_at_square (by norm_num only) hz hm
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    Nat.reduceAdd] at ht hc
  linarith only [ht, hc]

/-- On each of the four compressed radius intervals in section 122, the
linear loss plus the conductor and Euler costs is bounded at the right endpoint.
The endpoint certificates and the logarithmic slope give coverage between endpoints. -/
theorem quarter_euler_rows_644 {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    0.03138163 * r + (quarterConductor644 r + 4 * positiveTail644 (r ^ 2)) ≤
      if r ≤ 320 then 0.03138163 * 320 + 2.448593
      else
        if r ≤ 1287 / 4 then 0.03138163 * (1287 / 4) + 2.442030
        else
          if r ≤ 1609 / 5 then 0.03138163 * (1609 / 5) + 2.441843
          else 0.03138163 * 322 + 2.441096 := by
  by_cases h₁ : r ≤ 320
  · rw [ite_eq_left h₁]
    exact
      quarter_euler_loss_644 le_rfl ⟨hr.1, h₁⟩ (by norm_num only) quarter_euler_644_316
        quarter_euler_644_320 (by norm_num only)
  rw [ite_eq_right h₁]
  by_cases h₂ : r ≤ 1287 / 4
  · rw [ite_eq_left h₂]
    exact
      quarter_euler_loss_644 (by norm_num only) ⟨(le_of_not_ge h₁), h₂⟩ (by norm_num only)
        quarter_euler_644_320 quarter_euler_644_32175 (by norm_num only)
  rw [ite_eq_right h₂]
  by_cases h₃ : r ≤ 1609 / 5
  · rw [ite_eq_left h₃]
    exact
      quarter_euler_loss_644 (by norm_num only) ⟨(le_of_not_ge h₂), h₃⟩ (by norm_num only)
        quarter_euler_644_32175 quarter_euler_644_3218 (by norm_num only)
  rw [ite_eq_right h₃]
  exact
    quarter_euler_loss_644 (by norm_num only) ⟨(le_of_not_ge h₃), hr.2⟩ (by norm_num only)
      quarter_euler_644_3218 quarter_euler_644_322 (by norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
