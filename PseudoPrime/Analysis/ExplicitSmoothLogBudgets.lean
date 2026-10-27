/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! # Explicit logarithmic margins for rational smooth-product bounds -/

public section

namespace PseudoPrime.Analysis

/-- For z≥10^12, the quadratic exponential lower bound gives
32z≤exp(z/2000). This absorbs the fixed prime-supply loss at exponent
gap 1/2000, without any asymptotic threshold choice. -/
theorem thirty_two_mul_le_exp_div_two_thousand {z : ℝ} (hz : 10 ^ 12 ≤ z) :
    32 * z ≤ Real.exp (z / 2000) := by
  have hz0 : 0 ≤ z := le_trans (by norm_num only) hz
  have he := Real.quadratic_le_exp_of_nonneg (div_nonneg hz0 (by norm_num only : (0 : ℝ) ≤ 2000))
  have hm := mul_nonneg hz0 (sub_nonneg.mpr hz)
  nlinarith only [he, hm, hz]

/-- For z≥2 billion, the quadratic exponential lower bound gives
32z≤exp(z/5000). This supplies the smaller exponent gap used by the
rational cutoff's prime-count estimate. -/
theorem thirty_two_mul_le_exp_div_five_thousand {z : ℝ} (hz : 2000000000 ≤ z) :
    32 * z ≤ Real.exp (z / 5000) := by
  have hz0 : 0 ≤ z := le_trans (by norm_num only) hz
  have he := Real.quadratic_le_exp_of_nonneg (div_nonneg hz0 (by norm_num only : (0 : ℝ) ≤ 5000))
  have hm := mul_nonneg hz0 (sub_nonneg.mpr hz)
  nlinarith only [he, hm, hz]

/-- For z≥387 billion, applying the quadratic exponential lower bound at
half the argument gives a fourth-power bound that absorbs 32z at gap 10^-6. -/
theorem thirty_two_mul_le_exp_gap_million {z : ℝ} (hz : 387000000000 ≤ z) :
    32 * z ≤ Real.exp (z * (1 / 1000000 : ℝ)) := by
  have hz0 : 0 ≤ z := le_trans (by norm_num only) hz
  let x : ℝ := z * (1 / 1000000 : ℝ)
  have hx : 387000 ≤ x := by
    dsimp only [x]; nlinarith only [hz]
  have hx0 : 0 ≤ x := le_trans (by norm_num only) hx
  have hquad := Real.quadratic_le_exp_of_nonneg (div_nonneg hx0 (by norm_num only : (0 : ℝ) ≤ 2))
  have hsmall : x ^ 2 / 8 ≤ Real.exp (x / 2) := by nlinarith only [hquad, hx0]
  have hexp : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hquartic : x ^ 4 / 64 ≤ Real.exp x := by
    rw [hexp]
    have hmul := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ x ^ 2 / 8)
    nlinarith only [hmul, hsmall]
  have hsq : (387000 : ℝ) ^ 2 ≤ x ^ 2 := by
    have hprod :=
      mul_nonneg (sub_nonneg.mpr hx) (add_nonneg hx0 (by norm_num only : (0 : ℝ) ≤ 387000))
    nlinarith only [hprod]
  have hcube : 2048000000 ≤ x ^ 3 := by
    have hm := mul_le_mul_of_nonneg_right hsq hx0
    nlinarith only [hm, hx, hsq]
  have hfour : 32 * z ≤ x ^ 4 / 64 := by
    have hz_eq : z = 1000000 * x := by
      dsimp only [x]; ring
    rw [hz_eq]
    have hmul := mul_le_mul_of_nonneg_right hcube hx0
    nlinarith only [hmul]
  calc
    _ ≤ x ^ 4 / 64 := hfour
    _ ≤ Real.exp x := hquartic
    _ = Real.exp (z * (1 / 1000000 : ℝ)) := by rfl

/-- If L≥10^20 and log L≥10^11, the smooth-product logarithmic margin
holds at scale 125/68 for exponent 1838239/1000000 and coefficient 999997/1000000.
The quadratic lower bound for exp(log L) controls the remaining log L term. -/
theorem explicit_smooth_scale_125_68_gap {L : ℝ} (hL : 10 ^ 20 ≤ L) (hz : 10 ^ 11 ≤ Real.log L) :
    (999997 / 1000000 : ℝ) * (1838239 / 1000000) * L + (1838239 / 1000000 : ℝ) * Real.log L <
      (125 / 68) * L := by
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hz0 : 0 ≤ Real.log L := le_trans (by norm_num only) hz
  have hzpos : 0 < Real.log L :=
    Real.log_pos (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 10 ^ 20) hL)
  have hsq : (Real.log L) ^ 2 ≤ 2 * L := by
    have he := Real.quadratic_le_exp_of_nonneg hz0
    rw [Real.exp_log hLpos] at he
    nlinarith only [he, hz0]
  have hratio : Real.log L / L ≤ 2 / Real.log L := by
    apply (div_le_div_iff₀ hLpos hzpos).2
    nlinarith only [hsq]
  have hrecip : 1 / Real.log L ≤ 1 / (10 ^ 11 : ℝ) := by
    apply (div_le_div_iff₀ hzpos (by norm_num only : (0 : ℝ) < 10 ^ 11)).2
    nlinarith only [hz]
  have hsmall : Real.log L / L ≤ 2 / (10 ^ 11 : ℝ) := by
    calc
      _ ≤ 2 / Real.log L := hratio
      _ = 2 * (1 / Real.log L) := by ring
      _ ≤ 2 * (1 / (10 ^ 11 : ℝ)) := mul_le_mul_of_nonneg_left hrecip (by norm_num only)
      _ = _ := by ring
  have hscaled :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsmall (by norm_num only : (0 : ℝ) ≤ 1838239 / 1000000)) hLpos.le
  have hlog :
    (1838239 / 1000000 : ℝ) * Real.log L ≤ ((1838239 / 1000000 : ℝ) * (2 / 10 ^ 11)) * L := by
    calc
      _ = (1838239 / 1000000 : ℝ) * ((Real.log L / L) * L) := by rw [div_mul_cancel₀ _ hLpos.ne']
      _ = (1838239 / 1000000 : ℝ) * (Real.log L / L) * L := by ring
      _ ≤ _ := hscaled
  have hconst :
    (999997 / 1000000 : ℝ) * (1838239 / 1000000) + (1838239 / 1000000 : ℝ) * (2 / 10 ^ 11) <
      125 / 68 := by
    norm_num only
  have hmargin := mul_lt_mul_of_pos_right hconst hLpos
  nlinarith only [hlog, hmargin]

/-- For z≥10^11, the quartic exponential lower bound absorbs 32z at
exponent gap 1/10^6. This smaller explicit threshold supports the 74/40
finite-fiber scale. -/
theorem thirty_two_mul_le_exp_gap_million_of_hundred_billion {z : ℝ} (hz : 100000000000 ≤ z) :
    32 * z ≤ Real.exp (z * (1 / 1000000 : ℝ)) := by
  have hz0 : 0 ≤ z := le_trans (by norm_num only) hz
  let x : ℝ := z * (1 / 1000000 : ℝ)
  have hx : 100000 ≤ x := by
    dsimp only [x]; nlinarith only [hz]
  have hx0 : 0 ≤ x := le_trans (by norm_num only) hx
  have hquad := Real.quadratic_le_exp_of_nonneg (div_nonneg hx0 (by norm_num only : (0 : ℝ) ≤ 2))
  have hsmall : x ^ 2 / 8 ≤ Real.exp (x / 2) := by nlinarith only [hquad, hx0]
  have hexp : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hquartic : x ^ 4 / 64 ≤ Real.exp x := by
    rw [hexp]
    have hmul := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ x ^ 2 / 8)
    nlinarith only [hmul, hsmall]
  have hsq : (100000 : ℝ) ^ 2 ≤ x ^ 2 := by
    have hprod :=
      mul_nonneg (sub_nonneg.mpr hx) (add_nonneg hx0 (by norm_num only : (0 : ℝ) ≤ 100000))
    nlinarith only [hprod]
  have hcube : 2048000000 ≤ x ^ 3 := by
    have hm := mul_le_mul_of_nonneg_right hsq hx0
    nlinarith only [hm, hx, hsq]
  have hfour : 32 * z ≤ x ^ 4 / 64 := by
    have hz_eq : z = 1000000 * x := by
      dsimp only [x]; ring
    rw [hz_eq]
    have hmul := mul_le_mul_of_nonneg_right hcube hx0
    nlinarith only [hmul]
  calc
    _ ≤ x ^ 4 / 64 := hfour
    _ ≤ Real.exp x := hquartic
    _ = Real.exp (z * (1 / 1000000 : ℝ)) := by rfl

/-- For z≥2 billion, the quartic exponential lower bound absorbs 32z
at exponent gap 1/10^6. This threshold supports the 19/10 scale. -/
theorem thirty_two_mul_le_exp_gap_million_of_two_billion {z : ℝ} (hz : 2000000000 ≤ z) :
    32 * z ≤ Real.exp (z * (1 / 1000000 : ℝ)) := by
  have hz0 : 0 ≤ z := le_trans (by norm_num only) hz
  let x : ℝ := z * (1 / 1000000 : ℝ)
  have hx : 2000 ≤ x := by
    dsimp only [x]; nlinarith only [hz]
  have hx0 : 0 ≤ x := le_trans (by norm_num only) hx
  have hquad := Real.quadratic_le_exp_of_nonneg (div_nonneg hx0 (by norm_num only : (0 : ℝ) ≤ 2))
  have hsmall : x ^ 2 / 8 ≤ Real.exp (x / 2) := by nlinarith only [hquad, hx0]
  have hexp : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hquartic : x ^ 4 / 64 ≤ Real.exp x := by
    rw [hexp]
    have hmul := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ x ^ 2 / 8)
    nlinarith only [hmul, hsmall]
  have hsq : (2000 : ℝ) ^ 2 ≤ x ^ 2 := by
    have hprod :=
      mul_nonneg (sub_nonneg.mpr hx) (add_nonneg hx0 (by norm_num only : (0 : ℝ) ≤ 2000))
    nlinarith only [hprod]
  have hcube : 2048000000 ≤ x ^ 3 := by
    have hm := mul_le_mul_of_nonneg_right hsq hx0
    nlinarith only [hm, hx, hsq]
  have hfour : 32 * z ≤ x ^ 4 / 64 := by
    have hz_eq : z = 1000000 * x := by
      dsimp only [x]; ring
    rw [hz_eq]
    have hmul := mul_le_mul_of_nonneg_right hcube hx0
    nlinarith only [hmul]
  calc
    _ ≤ x ^ 4 / 64 := hfour
    _ ≤ Real.exp x := hquartic
    _ = Real.exp (z * (1 / 1000000 : ℝ)) := by rfl

/-- A rational binomial lower bound gives exp(25.31964)≥98,688,000,000. -/
theorem exp_632991_over_25000_ge_98688000000 :
    (98688000000 : ℝ) ≤ Real.exp (632991 / 25000 : ℝ) := by
  let x0 : ℝ := (3084000000 : ℝ) * (821 / 100000000000 : ℝ)
  let y : ℝ := x0 / 100000
  have hx00 : (632991 / 25000 : ℝ) = x0 := by
    dsimp only [x0]; norm_num only
  have hy : (2531964 / 10000000000 : ℝ) ≤ y := by
    rw [show y = x0 / 100000 by rfl, ← hx00]
    norm_num only
  have hbase : (250063299 / 250000000 : ℝ) ≤ 1 + y := by linarith only [hy]
  have hbaseExp : (250063299 / 250000000 : ℝ) ≤ Real.exp y := by
    calc
      _ ≤ 1 + y := hbase
      _ = y + 1 := by ring
      _ ≤ Real.exp y := Real.add_one_le_exp y
  have h100 : (1025639 / 1000000 : ℝ) ≤ (250063299 / 250000000 : ℝ) ^ 100 := by
    norm_num only [pow_succ]
  have h10 : (1288087 / 1000000 : ℝ) ≤ (1025639 / 1000000 : ℝ) ^ 10 := by norm_num only [pow_succ]
  have hfinal : (98688000000 : ℝ) ≤ (1288087 / 1000000 : ℝ) ^ 100 := by norm_num only [pow_succ]
  have h1000 : (1288087 / 1000000 : ℝ) ≤ (250063299 / 250000000 : ℝ) ^ 1000 := by
    calc
      _ ≤ ((1025639 / 1000000 : ℝ) ^ 10) := h10
      _ ≤ (((250063299 / 250000000 : ℝ) ^ 100) ^ 10) :=
        pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 1025639 / 1000000) h100 10
      _ = (250063299 / 250000000 : ℝ) ^ 1000 := by rw [← pow_mul]
  have hpow : (98688000000 : ℝ) ≤ (250063299 / 250000000 : ℝ) ^ 100000 := by
    calc
      _ ≤ ((1288087 / 1000000 : ℝ) ^ 100) := hfinal
      _ ≤ (((250063299 / 250000000 : ℝ) ^ 1000) ^ 100) :=
        pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 1288087 / 1000000) h1000 100
      _ = (250063299 / 250000000 : ℝ) ^ 100000 := by rw [← pow_mul]
  have hbasePow : (98688000000 : ℝ) ≤ Real.exp y ^ 100000 := by
    exact
      le_trans hpow
        (pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 250063299 / 250000000) hbaseExp 100000)
  have hexp0 : Real.exp x0 = Real.exp y ^ 100000 := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp only [y]
    ring
  rw [hx00, hexp0]
  exact hbasePow

/-- A million-step rational binomial lower bound for the refined exponent-gap anchor. -/
theorem exp_158222307_over_6250000_ge_98688000000 :
    (98688000000 : ℝ) ≤ Real.exp (158222307 / 6250000 : ℝ) := by
  let x0 : ℝ := (3084000000 : ℝ) * (820868 / 100000000000000 : ℝ)
  let y : ℝ := x0 / 1000000
  have hx00 : (158222307 / 6250000 : ℝ) = x0 := by
    dsimp only [x0]
    norm_num only
  have hbase : (100002531556912 / 100000000000000 : ℝ) ≤ 1 + y := by
    dsimp only [y, x0]
    norm_num only
  have hbaseExp : (100002531556912 / 100000000000000 : ℝ) ≤ Real.exp y := by
    calc
      _ ≤ 1 + y := hbase
      _ = y + 1 := by ring
      _ ≤ Real.exp y := Real.add_one_le_exp y
  have h100 :
    (1002534731883 / 1000000000000 : ℝ) ≤ (100002531556912 / 100000000000000 : ℝ) ^ 100 := by
    norm_num only [pow_succ]
  have h1000small :
    (1025638400719 / 1000000000000 : ℝ) ≤ (1002534731883 / 1000000000000 : ℝ) ^ 10 := by
    norm_num only [pow_succ]
  have h10000small :
    (1288079677034 / 1000000000000 : ℝ) ≤ (1025638400719 / 1000000000000 : ℝ) ^ 10 := by
    norm_num only [pow_succ]
  have hfinal : (98688000000 : ℝ) ≤ (1288079677034 / 1000000000000 : ℝ) ^ 100 := by
    norm_num only [pow_succ]
  have h1000 :
    (1025638400719 / 1000000000000 : ℝ) ≤ (100002531556912 / 100000000000000 : ℝ) ^ 1000 := by
    calc
      _ ≤ ((1002534731883 / 1000000000000 : ℝ) ^ 10) := h1000small
      _ ≤ (((100002531556912 / 100000000000000 : ℝ) ^ 100) ^ 10) :=
        pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 1002534731883 / 1000000000000) h100 10
      _ = (100002531556912 / 100000000000000 : ℝ) ^ 1000 := by rw [← pow_mul]
  have h10000 :
    (1288079677034 / 1000000000000 : ℝ) ≤ (100002531556912 / 100000000000000 : ℝ) ^ 10000 := by
    calc
      _ ≤ ((1025638400719 / 1000000000000 : ℝ) ^ 10) := h10000small
      _ ≤ (((100002531556912 / 100000000000000 : ℝ) ^ 1000) ^ 10) :=
        pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 1025638400719 / 1000000000000) h1000 10
      _ = (100002531556912 / 100000000000000 : ℝ) ^ 10000 := by rw [← pow_mul]
  have hpow : (98688000000 : ℝ) ≤ (100002531556912 / 100000000000000 : ℝ) ^ 1000000 := by
    calc
      _ ≤ ((1288079677034 / 1000000000000 : ℝ) ^ 100) := hfinal
      _ ≤ (((100002531556912 / 100000000000000 : ℝ) ^ 10000) ^ 100) :=
        pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 1288079677034 / 1000000000000) h10000 100
      _ = (100002531556912 / 100000000000000 : ℝ) ^ 1000000 := by rw [← pow_mul]
  have hb100000 : (100002531556912 / 100000000000000 : ℝ) ^ 100000 ≤ Real.exp y ^ 100000 :=
    pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 100002531556912 / 100000000000000) hbaseExp
      100000
  have hbasePow : (98688000000 : ℝ) ≤ Real.exp y ^ 1000000 := by
    calc
      _ ≤ (100002531556912 / 100000000000000 : ℝ) ^ 1000000 := hpow
      _ = ((100002531556912 / 100000000000000 : ℝ) ^ 100000) ^ 10 := by rw [← pow_mul]
      _ ≤ (Real.exp y ^ 100000) ^ 10 := pow_le_pow_left₀ (by positivity) hb100000 10
      _ = Real.exp y ^ 1000000 := by rw [← pow_mul]
  have hexp0 : Real.exp x0 = Real.exp y ^ 1000000 := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp only [y]
    ring
  rw [hx00, hexp0]
  exact hbasePow

/-- For z≥3,084,000,000, a million-step rational binomial bound absorbs 32z
at exponent gap 820868/100000000000000. -/
theorem thirty_two_mul_le_exp_gap_820868 {z : ℝ} (hz : 3084000000 ≤ z) :
    32 * z ≤ Real.exp (z * (820868 / 100000000000000 : ℝ)) := by
  let x : ℝ := z * (820868 / 100000000000000 : ℝ)
  let x0 : ℝ := (3084000000 : ℝ) * (820868 / 100000000000000 : ℝ)
  have hx0 : x0 ≤ x := by
    dsimp only [x, x0]; nlinarith only [hz]
  have hx00 : (158222307 / 6250000 : ℝ) = x0 := by
    dsimp only [x0]; norm_num only
  have hanchor : (98688000000 : ℝ) ≤ Real.exp x0 := by
    rw [← hx00]
    exact exp_158222307_over_6250000_ge_98688000000
  have hscale : z ≤ (3084000000 : ℝ) * (1 + (x - x0)) := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hnonneg : 0 ≤ 1 + (x - x0) := by linarith only [hx0]
  have hscaled := mul_le_mul_of_nonneg_right hanchor hnonneg
  have hleft : 32 * z ≤ Real.exp x0 * (1 + (x - x0)) := by nlinarith only [hscale, hscaled]
  have hdelta := Real.add_one_le_exp (x - x0)
  have hright := mul_le_mul_of_nonneg_left hdelta (Real.exp_nonneg x0)
  have hexp : Real.exp x = Real.exp x0 * Real.exp (x - x0) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    32 * z ≤ Real.exp x0 * (1 + (x - x0)) := hleft
    _ ≤ Real.exp x0 * Real.exp (x - x0) := by simpa only [add_comm] using hright
    _ = Real.exp x := hexp.symm

/-- For z≥3,084,000,000, a rational binomial lower bound absorbs 32z at
exponent gap 821/100000000000. -/
theorem thirty_two_mul_le_exp_gap_821 {z : ℝ} (hz : 3084000000 ≤ z) :
    32 * z ≤ Real.exp (z * (821 / 100000000000 : ℝ)) := by
  let x : ℝ := z * (821 / 100000000000 : ℝ)
  let x0 : ℝ := (3084000000 : ℝ) * (821 / 100000000000 : ℝ)
  have hx0 : x0 ≤ x := by
    dsimp only [x, x0]; nlinarith only [hz]
  have hx00 : (632991 / 25000 : ℝ) = x0 := by
    dsimp only [x0]; norm_num only
  have hanchor : (98688000000 : ℝ) ≤ Real.exp x0 := by
    rw [← hx00]
    exact exp_632991_over_25000_ge_98688000000
  have hscale : z ≤ (3084000000 : ℝ) * (1 + (x - x0)) := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hnonneg : 0 ≤ 1 + (x - x0) := by linarith only [hx0]
  have hscaled := mul_le_mul_of_nonneg_right hanchor hnonneg
  have hleft : 32 * z ≤ Real.exp x0 * (1 + (x - x0)) := by nlinarith only [hscale, hscaled]
  have hdelta := Real.add_one_le_exp (x - x0)
  have hright := mul_le_mul_of_nonneg_left hdelta (Real.exp_nonneg x0)
  have hexp : Real.exp x = Real.exp x0 * Real.exp (x - x0) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    32 * z ≤ Real.exp x0 * (1 + (x - x0)) := hleft
    _ ≤ Real.exp x0 * Real.exp (x - x0) := by simpa only [add_comm] using hright
    _ = Real.exp x := hexp.symm

/-- For z≥53,000,000, the gap 1/2,000,000 absorbs the prime-counting loss
32z. Anchor the exponential at 53/2 using exp(1)≥(64/27). -/
theorem thirty_two_mul_le_exp_gap_half_million {z : ℝ} (hz : 53000000 ≤ z) :
    32 * z ≤ Real.exp (z * (1 / 2000000 : ℝ)) := by
  let x : ℝ := z * (1 / 2000000 : ℝ)
  let x0 : ℝ := 53 / 2
  have hx0 : x0 ≤ x := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hthird : (4 / 3 : ℝ) ≤ Real.exp (1 / 3) := by
    have h := Real.add_one_le_exp (1 / 3 : ℝ)
    nlinarith only [h]
  have hcube : (4 / 3 : ℝ) ^ 3 ≤ Real.exp (1 / 3) ^ 3 :=
    pow_le_pow_left₀ (by norm_num only) hthird 3
  have hE : (64 / 27 : ℝ) ≤ Real.exp 1 := by
    have hmul : Real.exp (1 / 3) ^ 3 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num only
    simpa only [show (4 / 3 : ℝ) ^ 3 = 64 / 27 by norm_num only, hmul] using hcube
  have hpow : (64 / 27 : ℝ) ^ 26 ≤ Real.exp 1 ^ 26 := pow_le_pow_left₀ (by norm_num only) hE 26
  have hexp26 : Real.exp 1 ^ 26 = Real.exp 26 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num only
  have hx0lower : (1696000000 : ℝ) ≤ Real.exp x0 := by
    have hmono := Real.exp_le_exp.mpr (by norm_num only : (26 : ℝ) ≤ x0)
    have hn : (1696000000 : ℝ) ≤ (64 / 27 : ℝ) ^ 26 := by norm_num only
    exact hn.trans (hpow.trans_eq hexp26 |>.trans hmono)
  have hscale : z ≤ (53000000 : ℝ) * (1 + (x - x0)) := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hnonneg : 0 ≤ 1 + (x - x0) := by linarith only [hx0]
  have hscaled := mul_le_mul_of_nonneg_right hx0lower hnonneg
  have hleft : 32 * z ≤ Real.exp x0 * (1 + (x - x0)) := by nlinarith only [hscale, hscaled]
  have hdelta := Real.add_one_le_exp (x - x0)
  have hright := mul_le_mul_of_nonneg_left hdelta (Real.exp_nonneg x0)
  have hexp : Real.exp x = Real.exp x0 * Real.exp (x - x0) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    32 * z ≤ Real.exp x0 * (1 + (x - x0)) := hleft
    _ ≤ Real.exp x0 * Real.exp (x - x0) := by simpa only [add_comm] using hright
    _ = Real.exp x := hexp.symm

/-- At the tightened 76697551 threshold, the double-log lower bound lets the
prime-counting loss 32z be absorbed with exponent gap 1/2500000. The anchor
uses the first three terms at the remaining rational part of the exponent. -/
theorem thirty_two_mul_le_exp_gap_two_million_five_hundred_thousand {z : ℝ} (hz : 53162690 ≤ z) :
    32 * z ≤ Real.exp (z * (1 / 2500000 : ℝ)) := by
  let x : ℝ := z * (1 / 2500000 : ℝ)
  let x0 : ℝ := 53162690 / 2500000
  have hx0 : x0 ≤ x := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hE1 : (1957 / 720 : ℝ) ≤ Real.exp 1 := by
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1) 7
    have heq : (∑ k ∈ Finset.range 7, (1 : ℝ) ^ k / k.factorial) = 1957 / 720 := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
        Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
    exact heq.symm.le.trans hsum
  have hEpow : (1957 / 720 : ℝ) ^ 21 ≤ Real.exp 1 ^ 21 := pow_le_pow_left₀ (by norm_num only) hE1 21
  have hE21 : (1957 / 720 : ℝ) ^ 21 ≤ Real.exp 21 := by
    calc
      _ ≤ Real.exp 1 ^ 21 := hEpow
      _ = Real.exp 21 := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num only
  have hrem :
    (1 + (66269 / 250000 : ℝ) + (66269 / 250000 : ℝ) ^ 2 / 2) ≤ Real.exp (66269 / 250000 : ℝ) := by
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 66269 / 250000) 3
    have heq :
      (∑ k ∈ Finset.range 3, (66269 / 250000 : ℝ) ^ k / k.factorial) =
        1 + (66269 / 250000 : ℝ) + (66269 / 250000 : ℝ) ^ 2 / 2 := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
        Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
    exact heq.symm.le.trans hsum
  have hprod :
    (1957 / 720 : ℝ) ^ 21 * (1 + (66269 / 250000 : ℝ) + (66269 / 250000 : ℝ) ^ 2 / 2) ≤
      Real.exp 21 * Real.exp (66269 / 250000 : ℝ) :=
    mul_le_mul hE21 hrem (by norm_num only) (Real.exp_pos _).le
  have hexp0 : Real.exp 21 * Real.exp (66269 / 250000 : ℝ) = Real.exp x0 := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [x0]
    norm_num only
  have hnum :
    (32 : ℝ) * 53162690 ≤
      (1957 / 720 : ℝ) ^ 21 * (1 + (66269 / 250000 : ℝ) + (66269 / 250000 : ℝ) ^ 2 / 2) := by
    norm_num only
  have hanchor : (32 : ℝ) * 53162690 ≤ Real.exp x0 := hnum.trans (hprod.trans_eq hexp0)
  have hscale : z ≤ 53162690 * (1 + (x - x0)) := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hnonneg : 0 ≤ 1 + (x - x0) := by linarith only [hx0]
  have hscaled := mul_le_mul_of_nonneg_right hanchor hnonneg
  have hleft : 32 * z ≤ Real.exp x0 * (1 + (x - x0)) := by nlinarith only [hscale, hscaled]
  have hdelta := Real.add_one_le_exp (x - x0)
  have hright := mul_le_mul_of_nonneg_left hdelta (Real.exp_nonneg x0)
  have hexp : Real.exp x = Real.exp x0 * Real.exp (x - x0) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    32 * z ≤ Real.exp x0 * (1 + (x - x0)) := hleft
    _ ≤ Real.exp x0 * Real.exp (x - x0) := by simpa only [add_comm] using hright
    _ = Real.exp x := hexp.symm

/-- At the 53-million double-log scale, exponent gap 388/1,000,000,000
absorbs the prime-counting loss 16z. The anchor is 20+141/250. The
exponential series supplies lower bounds at both pieces of the anchor. -/
theorem sixteen_mul_le_exp_gap_388_over_billion {z : ℝ} (hz : 53000000 ≤ z) :
    16 * z ≤ Real.exp (z * (388 / 1000000000 : ℝ)) := by
  let x : ℝ := z * (388 / 1000000000 : ℝ)
  let x0 : ℝ := 5141 / 250
  have hx0 : x0 ≤ x := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hE1 : (685 / 252 : ℝ) ≤ Real.exp 1 := by
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1) 8
    have heq : (∑ k ∈ Finset.range 8, (1 : ℝ) ^ k / k.factorial) = 685 / 252 := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
        Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
    exact heq.symm.le.trans hsum
  have hEpow : (685 / 252 : ℝ) ^ 20 ≤ Real.exp 1 ^ 20 := pow_le_pow_left₀ (by norm_num only) hE1 20
  have hE20 : (685 / 252 : ℝ) ^ 20 ≤ Real.exp 20 := by
    calc
      _ ≤ Real.exp 1 ^ 20 := hEpow
      _ = Real.exp 20 := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num only
  have hrem :
    (1 + (141 / 250 : ℝ) + (141 / 250 : ℝ) ^ 2 / 2 + (141 / 250 : ℝ) ^ 3 / 6) ≤
      Real.exp (141 / 250 : ℝ) := by
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 141 / 250) 4
    have heq :
      (∑ k ∈ Finset.range 4, (141 / 250 : ℝ) ^ k / k.factorial) =
        1 + (141 / 250 : ℝ) + (141 / 250 : ℝ) ^ 2 / 2 + (141 / 250 : ℝ) ^ 3 / 6 := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
        Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
    exact heq.symm.le.trans hsum
  have hprod :
    (685 / 252 : ℝ) ^ 20 *
        (1 + (141 / 250 : ℝ) + (141 / 250 : ℝ) ^ 2 / 2 + (141 / 250 : ℝ) ^ 3 / 6) ≤
      Real.exp 20 * Real.exp (141 / 250 : ℝ) :=
    mul_le_mul hE20 hrem (by norm_num only) (Real.exp_pos _).le
  have hexp0 : Real.exp 20 * Real.exp (141 / 250 : ℝ) = Real.exp x0 := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [x0]
    norm_num only
  have hnum :
    (16 : ℝ) * 53000000 ≤
      (685 / 252 : ℝ) ^ 20 *
        (1 + (141 / 250 : ℝ) + (141 / 250 : ℝ) ^ 2 / 2 + (141 / 250 : ℝ) ^ 3 / 6) := by
    norm_num only
  have hanchor : (16 : ℝ) * 53000000 ≤ Real.exp x0 := hnum.trans (hprod.trans_eq hexp0)
  have hscale : z ≤ (53000000 : ℝ) * (1 + (x - x0)) := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hnonneg : 0 ≤ 1 + (x - x0) := by linarith only [hx0]
  have hscaled := mul_le_mul_of_nonneg_right hanchor hnonneg
  have hleft : 16 * z ≤ Real.exp x0 * (1 + (x - x0)) := by nlinarith only [hscale, hscaled]
  have hdelta := Real.add_one_le_exp (x - x0)
  have hright := mul_le_mul_of_nonneg_left hdelta (Real.exp_nonneg x0)
  have hexp : Real.exp x = Real.exp x0 * Real.exp (x - x0) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    16 * z ≤ Real.exp x0 * (1 + (x - x0)) := hleft
    _ ≤ Real.exp x0 * Real.exp (x - x0) := by simpa only [add_comm] using hright
    _ = Real.exp x := hexp.symm

/-- At the 53-million double-log scale, exponent gap $771/(2\cdot10^9)$
absorbs the prime-counting loss $14z$. The anchor is $20+863/2000$.
Finite exponential series bounds certify the anchor. -/
theorem fourteen_mul_le_exp_gap_771_over_2_billion {z : ℝ} (hz : 53000000 ≤ z) :
    14 * z ≤ Real.exp (z * (771 / 2000000000 : ℝ)) := by
  let x : ℝ := z * (771 / 2000000000 : ℝ)
  let x0 : ℝ := 40863 / 2000
  have hx0 : x0 ≤ x := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hE1 : (685 / 252 : ℝ) ≤ Real.exp 1 := by
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1) 8
    have heq : (∑ k ∈ Finset.range 8, (1 : ℝ) ^ k / k.factorial) = 685 / 252 := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
        Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
    exact heq.symm.le.trans hsum
  have hEpow : (685 / 252 : ℝ) ^ 20 ≤ Real.exp 1 ^ 20 := pow_le_pow_left₀ (by norm_num only) hE1 20
  have hE20 : (685 / 252 : ℝ) ^ 20 ≤ Real.exp 20 := by
    calc
      _ ≤ Real.exp 1 ^ 20 := hEpow
      _ = Real.exp 20 := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num only
  have hrem :
    (1 + (863 / 2000 : ℝ) + (863 / 2000 : ℝ) ^ 2 / 2 + (863 / 2000 : ℝ) ^ 3 / 6) ≤
      Real.exp (863 / 2000 : ℝ) := by
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 863 / 2000) 4
    have heq :
      (∑ k ∈ Finset.range 4, (863 / 2000 : ℝ) ^ k / k.factorial) =
        1 + (863 / 2000 : ℝ) + (863 / 2000 : ℝ) ^ 2 / 2 + (863 / 2000 : ℝ) ^ 3 / 6 := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
        Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
    exact heq.symm.le.trans hsum
  have hprod :
    (685 / 252 : ℝ) ^ 20 *
        (1 + (863 / 2000 : ℝ) + (863 / 2000 : ℝ) ^ 2 / 2 + (863 / 2000 : ℝ) ^ 3 / 6) ≤
      Real.exp 20 * Real.exp (863 / 2000 : ℝ) :=
    mul_le_mul hE20 hrem (by norm_num only) (Real.exp_pos _).le
  have hexp0 : Real.exp 20 * Real.exp (863 / 2000 : ℝ) = Real.exp x0 := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [x0]
    norm_num only
  have hnum :
    (14 : ℝ) * 53000000 ≤
      (685 / 252 : ℝ) ^ 20 *
        (1 + (863 / 2000 : ℝ) + (863 / 2000 : ℝ) ^ 2 / 2 + (863 / 2000 : ℝ) ^ 3 / 6) := by
    norm_num only
  have hanchor : (14 : ℝ) * 53000000 ≤ Real.exp x0 := hnum.trans (hprod.trans_eq hexp0)
  have hscale : z ≤ (53000000 : ℝ) * (1 + (x - x0)) := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hnonneg : 0 ≤ 1 + (x - x0) := by linarith only [hx0]
  have hscaled := mul_le_mul_of_nonneg_right hanchor hnonneg
  have hleft : 14 * z ≤ Real.exp x0 * (1 + (x - x0)) := by nlinarith only [hscale, hscaled]
  have hdelta := Real.add_one_le_exp (x - x0)
  have hright := mul_le_mul_of_nonneg_left hdelta (Real.exp_nonneg x0)
  have hexp : Real.exp x = Real.exp x0 * Real.exp (x - x0) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    14 * z ≤ Real.exp x0 * (1 + (x - x0)) := hleft
    _ ≤ Real.exp x0 * Real.exp (x - x0) := by simpa only [add_comm] using hright
    _ = Real.exp x := hexp.symm

/-- At the 53-million double-log scale, exponent gap $3846/10^{10}$
absorbs the refined prime-counting loss $(13381/1000)z$. The anchor is
$20+3838/10000$, certified by finite exponential series bounds. -/
theorem thirteen_point_three_eight_one_mul_le_exp_gap_3846_over_10_billion {z : ℝ}
    (hz : 53000000 ≤ z) : (13381 / 1000 : ℝ) * z ≤ Real.exp (z * (3846 / 10000000000 : ℝ)) := by
  let x : ℝ := z * (3846 / 10000000000 : ℝ)
  let x0 : ℝ := 101919 / 5000
  have hx0 : x0 ≤ x := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hE1 : (685 / 252 : ℝ) ≤ Real.exp 1 := by
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1) 8
    have heq : (∑ k ∈ Finset.range 8, (1 : ℝ) ^ k / k.factorial) = 685 / 252 := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
        Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
    exact heq.symm.le.trans hsum
  have hEpow : (685 / 252 : ℝ) ^ 20 ≤ Real.exp 1 ^ 20 := pow_le_pow_left₀ (by norm_num only) hE1 20
  have hE20 : (685 / 252 : ℝ) ^ 20 ≤ Real.exp 20 := by
    calc
      _ ≤ Real.exp 1 ^ 20 := hEpow
      _ = Real.exp 20 := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num only
  have hrem :
    (1 + (3838 / 10000 : ℝ) + (3838 / 10000 : ℝ) ^ 2 / 2 + (3838 / 10000 : ℝ) ^ 3 / 6) ≤
      Real.exp (3838 / 10000 : ℝ) := by
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 3838 / 10000) 4
    have heq :
      (∑ k ∈ Finset.range 4, (3838 / 10000 : ℝ) ^ k / k.factorial) =
        1 + (3838 / 10000 : ℝ) + (3838 / 10000 : ℝ) ^ 2 / 2 + (3838 / 10000 : ℝ) ^ 3 / 6 := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
        Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
    exact heq.symm.le.trans hsum
  have hprod :
    (685 / 252 : ℝ) ^ 20 *
        (1 + (3838 / 10000 : ℝ) + (3838 / 10000 : ℝ) ^ 2 / 2 + (3838 / 10000 : ℝ) ^ 3 / 6) ≤
      Real.exp 20 * Real.exp (3838 / 10000 : ℝ) :=
    mul_le_mul hE20 hrem (by norm_num only) (Real.exp_pos _).le
  have hexp0 : Real.exp 20 * Real.exp (3838 / 10000 : ℝ) = Real.exp x0 := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [x0]
    norm_num only
  have hnum :
    (13381 / 1000 : ℝ) * 53000000 ≤
      (685 / 252 : ℝ) ^ 20 *
        (1 + (3838 / 10000 : ℝ) + (3838 / 10000 : ℝ) ^ 2 / 2 + (3838 / 10000 : ℝ) ^ 3 / 6) := by
    norm_num only
  have hanchor : (13381 / 1000 : ℝ) * 53000000 ≤ Real.exp x0 := hnum.trans (hprod.trans_eq hexp0)
  have hscale : z ≤ (53000000 : ℝ) * (1 + (x - x0)) := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hnonneg : 0 ≤ 1 + (x - x0) := by linarith only [hx0]
  have hscaled := mul_le_mul_of_nonneg_right hanchor hnonneg
  have hscaleK := mul_le_mul_of_nonneg_left hscale (by norm_num only : (0 : ℝ) ≤ 13381 / 1000)
  have hleft : (13381 / 1000 : ℝ) * z ≤ Real.exp x0 * (1 + (x - x0)) := by
    nlinarith only [hscaleK, hscaled]
  have hdelta := Real.add_one_le_exp (x - x0)
  have hright := mul_le_mul_of_nonneg_left hdelta (Real.exp_nonneg x0)
  have hexp : Real.exp x = Real.exp x0 * Real.exp (x - x0) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (13381 / 1000 : ℝ) * z ≤ Real.exp x0 * (1 + (x - x0)) := hleft
    _ ≤ Real.exp x0 * Real.exp (x - x0) := by simpa only [add_comm] using hright
    _ = Real.exp x := hexp.symm

/-- The earlier coefficient-gap estimate follows from the sharper bound above. -/
theorem thirteen_point_five_twelve_mul_le_exp_gap_3848_over_10_billion {z : ℝ} (hz : 53000000 ≤ z) :
    (1689 / 125 : ℝ) * z ≤ Real.exp (z * (3848 / 10000000000 : ℝ)) := by
  have hnew := thirteen_point_three_eight_one_mul_le_exp_gap_3846_over_10_billion hz
  have hdelta : (106 / 10000 : ℝ) ≤ z * (2 / 10000000000 : ℝ) := by nlinarith only [hz]
  have hextra : 1 + (106 / 10000 : ℝ) ≤ Real.exp (z * (2 / 10000000000 : ℝ)) := by
    calc
      _ ≤ 1 + z * (2 / 10000000000 : ℝ) := by simpa only [add_comm] using add_le_add_left hdelta 1
      _ ≤ Real.exp (z * (2 / 10000000000 : ℝ)) := by
        simpa only [add_comm] using Real.add_one_le_exp (z * (2 / 10000000000 : ℝ))
  have hcoeff : (1689 / 125 : ℝ) ≤ (13381 / 1000 : ℝ) * Real.exp (z * (2 / 10000000000 : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_left hextra (by norm_num only : (0 : ℝ) ≤ 13381 / 1000)
    have hr : (1689 / 125 : ℝ) ≤ (13381 / 1000 : ℝ) * (1 + 106 / 10000) := by norm_num only
    exact hr.trans hm
  have hz0 : 0 ≤ z := le_trans (by norm_num only) hz
  have hleft := mul_le_mul_of_nonneg_right hcoeff hz0
  have hprod := mul_le_mul_of_nonneg_left hnew (Real.exp_nonneg (z * (2 / 10000000000 : ℝ)))
  calc
    (1689 / 125 : ℝ) * z ≤ (13381 / 1000 : ℝ) * Real.exp (z * (2 / 10000000000 : ℝ)) * z := hleft
    _ = Real.exp (z * (2 / 10000000000 : ℝ)) * ((13381 / 1000 : ℝ) * z) := by ring
    _ ≤ Real.exp (z * (2 / 10000000000 : ℝ)) * Real.exp (z * (3846 / 10000000000 : ℝ)) := hprod
    _ = Real.exp (z * (3848 / 10000000000 : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- At double-log scale 14,900,000, exponent gap 14/10,000,000 absorbs the
prime-counting loss 32z. A rational Taylor lower bound at 20.86 proves the
anchor, and an exponential scaling argument covers the whole half-line. -/
theorem thirty_two_mul_le_exp_gap_fourteen_over_ten_million {z : ℝ} (hz : 14900000 ≤ z) :
    32 * z ≤ Real.exp (z * (14 / 10000000 : ℝ)) := by
  let x : ℝ := z * (14 / 10000000 : ℝ)
  let x0 : ℝ := 1043 / 50
  have hx0 : x0 ≤ x := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hE1 : (685 / 252 : ℝ) ≤ Real.exp 1 := by
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1) 8
    have heq : (∑ k ∈ Finset.range 8, (1 : ℝ) ^ k / k.factorial) = 685 / 252 := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
        Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
    exact heq.symm.le.trans hsum
  have hE20 : (685 / 252 : ℝ) ^ 20 ≤ Real.exp 20 := by
    calc
      _ ≤ Real.exp 1 ^ 20 := pow_le_pow_left₀ (by norm_num only) hE1 20
      _ = Real.exp 20 := by
        rw [← Real.exp_nat_mul]; congr 1; norm_num only
  have hrem :
    (1 + (43 / 50 : ℝ) + (43 / 50 : ℝ) ^ 2 / 2 + (43 / 50 : ℝ) ^ 3 / 6 + (43 / 50 : ℝ) ^ 4 / 24) ≤
      Real.exp (43 / 50 : ℝ) := by
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 43 / 50) 5
    have heq :
      (∑ k ∈ Finset.range 5, (43 / 50 : ℝ) ^ k / k.factorial) =
        1 + (43 / 50 : ℝ) + (43 / 50 : ℝ) ^ 2 / 2 + (43 / 50 : ℝ) ^ 3 / 6 +
          (43 / 50 : ℝ) ^ 4 / 24 := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
        Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
    exact heq.symm.le.trans hsum
  have hprod :
    (685 / 252 : ℝ) ^ 20 *
        (1 + (43 / 50 : ℝ) + (43 / 50 : ℝ) ^ 2 / 2 + (43 / 50 : ℝ) ^ 3 / 6 +
          (43 / 50 : ℝ) ^ 4 / 24) ≤
      Real.exp 20 * Real.exp (43 / 50 : ℝ) :=
    mul_le_mul hE20 hrem (by norm_num only) (Real.exp_pos _).le
  have hexp0 : Real.exp 20 * Real.exp (43 / 50 : ℝ) = Real.exp x0 := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [x0]
    norm_num only
  have hnum :
    (32 : ℝ) * 14900000 ≤
      (685 / 252 : ℝ) ^ 20 *
        (1 + (43 / 50 : ℝ) + (43 / 50 : ℝ) ^ 2 / 2 + (43 / 50 : ℝ) ^ 3 / 6 +
          (43 / 50 : ℝ) ^ 4 / 24) := by
    norm_num only
  have hanchor : (32 : ℝ) * 14900000 ≤ Real.exp x0 := hnum.trans (hprod.trans_eq hexp0)
  have hscale : z ≤ (14900000 : ℝ) * (1 + (x - x0)) := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hnonneg : 0 ≤ 1 + (x - x0) := by linarith only [hx0]
  have hscaled := mul_le_mul_of_nonneg_right hanchor hnonneg
  have hleft : 32 * z ≤ Real.exp x0 * (1 + (x - x0)) := by nlinarith only [hscale, hscaled]
  have hdelta := Real.add_one_le_exp (x - x0)
  have hright := mul_le_mul_of_nonneg_left hdelta (Real.exp_nonneg x0)
  have hexp : Real.exp x = Real.exp x0 * Real.exp (x - x0) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    32 * z ≤ Real.exp x0 * (1 + (x - x0)) := hleft
    _ ≤ Real.exp x0 * Real.exp (x - x0) := by simpa only [add_comm] using hright
    _ = Real.exp x := hexp.symm

/-- At double-log scale 12,082,601, exponent gap 17/10,000,000 absorbs the
prime-counting loss 32z. A rational Taylor lower bound at 20.5404 proves the
anchor, and exponential scaling covers the half-line. -/
theorem thirty_two_mul_le_exp_gap_seventeen_over_ten_million {z : ℝ} (hz : 12082601 ≤ z) :
    32 * z ≤ Real.exp (z * (17 / 10000000 : ℝ)) := by
  let x : ℝ := z * (17 / 10000000 : ℝ)
  let x0 : ℝ := 205404 / 10000
  have hx0 : x0 ≤ x := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hE1 : (685 / 252 : ℝ) ≤ Real.exp 1 := by
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1) 8
    have heq : (∑ k ∈ Finset.range 8, (1 : ℝ) ^ k / k.factorial) = 685 / 252 := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
        Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
    exact heq.symm.le.trans hsum
  have hE20 : (685 / 252 : ℝ) ^ 20 ≤ Real.exp 20 := by
    calc
      _ ≤ Real.exp 1 ^ 20 := pow_le_pow_left₀ (by norm_num only) hE1 20
      _ = Real.exp 20 := by
        rw [← Real.exp_nat_mul]; congr 1; norm_num only
  have hrem :
    (1 + (5404 / 10000 : ℝ) + (5404 / 10000 : ℝ) ^ 2 / 2 + (5404 / 10000 : ℝ) ^ 3 / 6 +
        (5404 / 10000 : ℝ) ^ 4 / 24) ≤
      Real.exp (5404 / 10000 : ℝ) := by
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 5404 / 10000) 5
    have heq :
      (∑ k ∈ Finset.range 5, (5404 / 10000 : ℝ) ^ k / k.factorial) =
        1 + (5404 / 10000 : ℝ) + (5404 / 10000 : ℝ) ^ 2 / 2 + (5404 / 10000 : ℝ) ^ 3 / 6 +
          (5404 / 10000 : ℝ) ^ 4 / 24 := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
        Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
    exact heq.symm.le.trans hsum
  have hprod :
    (685 / 252 : ℝ) ^ 20 *
        (1 + (5404 / 10000 : ℝ) + (5404 / 10000 : ℝ) ^ 2 / 2 + (5404 / 10000 : ℝ) ^ 3 / 6 +
          (5404 / 10000 : ℝ) ^ 4 / 24) ≤
      Real.exp 20 * Real.exp (5404 / 10000 : ℝ) :=
    mul_le_mul hE20 hrem (by norm_num only) (Real.exp_pos _).le
  have hexp0 : Real.exp 20 * Real.exp (5404 / 10000 : ℝ) = Real.exp x0 := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [x0]
    norm_num only
  have hnum :
    (32 : ℝ) * 12082601 ≤
      (685 / 252 : ℝ) ^ 20 *
        (1 + (5404 / 10000 : ℝ) + (5404 / 10000 : ℝ) ^ 2 / 2 + (5404 / 10000 : ℝ) ^ 3 / 6 +
          (5404 / 10000 : ℝ) ^ 4 / 24) := by
    norm_num only
  have hanchor : (32 : ℝ) * 12082601 ≤ Real.exp x0 := hnum.trans (hprod.trans_eq hexp0)
  have hscale : z ≤ (12082601 : ℝ) * (1 + (x - x0)) := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hnonneg : 0 ≤ 1 + (x - x0) := by linarith only [hx0]
  have hscaled := mul_le_mul_of_nonneg_right hanchor hnonneg
  have hleft : 32 * z ≤ Real.exp x0 * (1 + (x - x0)) := by nlinarith only [hscale, hscaled]
  have hdelta := Real.add_one_le_exp (x - x0)
  have hright := mul_le_mul_of_nonneg_left hdelta (Real.exp_nonneg x0)
  have hexp : Real.exp x = Real.exp x0 * Real.exp (x - x0) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    32 * z ≤ Real.exp x0 * (1 + (x - x0)) := hleft
    _ ≤ Real.exp x0 * Real.exp (x - x0) := by simpa only [add_comm] using hright
    _ = Real.exp x := hexp.symm

/-- Inputs: a real number z at least 12,082,601.
Claim: 32z is at most exp(1,637z/1,000,000,000).
Content: A rational Taylor lower bound at 19+779/1000 proves the anchor;
exponential scaling extends the inequality to the half-line.
Role: absorbs the prime-counting loss for the refined 28/15 witness branch. -/
theorem thirty_two_mul_le_exp_gap_1637_over_billion {z : ℝ} (hz : 12082601 ≤ z) :
    32 * z ≤ Real.exp (z * (1637 / 1000000000 : ℝ)) := by
  let x : ℝ := z * (1637 / 1000000000 : ℝ)
  let x0 : ℝ := 19 + 779217837 / 1000000000
  let x1 : ℝ := 19 + 779 / 1000
  have hx0 : x0 ≤ x := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hx1 : x1 ≤ x0 := by
    dsimp only [x0, x1]
    norm_num only
  have hE1 : (685 / 252 : ℝ) ≤ Real.exp 1 := by
    have hs := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1) 8
    have he : (∑ k ∈ Finset.range 8, (1 : ℝ) ^ k / k.factorial) = 685 / 252 := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
        Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
    exact he.symm.le.trans hs
  have hE19 : (685 / 252 : ℝ) ^ 19 ≤ Real.exp 19 := by
    calc
      _ ≤ Real.exp 1 ^ 19 := pow_le_pow_left₀ (by norm_num only) hE1 19
      _ = Real.exp 19 := by
        rw [← Real.exp_nat_mul]; congr 1; norm_num only
  have hrem :
    (1 + (779 / 1000 : ℝ) + (779 / 1000 : ℝ) ^ 2 / 2 + (779 / 1000 : ℝ) ^ 3 / 6 +
        (779 / 1000 : ℝ) ^ 4 / 24) ≤
      Real.exp (779 / 1000 : ℝ) := by
    have hs := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 779 / 1000) 5
    have he :
      (∑ k ∈ Finset.range 5, (779 / 1000 : ℝ) ^ k / k.factorial) =
        1 + (779 / 1000 : ℝ) + (779 / 1000 : ℝ) ^ 2 / 2 + (779 / 1000 : ℝ) ^ 3 / 6 +
          (779 / 1000 : ℝ) ^ 4 / 24 := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
        Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
    exact he.symm.le.trans hs
  have hprod :
    (685 / 252 : ℝ) ^ 19 *
        (1 + (779 / 1000 : ℝ) + (779 / 1000 : ℝ) ^ 2 / 2 + (779 / 1000 : ℝ) ^ 3 / 6 +
          (779 / 1000 : ℝ) ^ 4 / 24) ≤
      Real.exp 19 * Real.exp (779 / 1000 : ℝ) :=
    mul_le_mul hE19 hrem (by norm_num only) (Real.exp_pos _).le
  have hexp1 : Real.exp 19 * Real.exp (779 / 1000 : ℝ) = Real.exp (19 + 779 / 1000 : ℝ) :=
    (Real.exp_add 19 (779 / 1000 : ℝ)).symm
  have hn :
    (32 : ℝ) * 12082601 ≤
      (685 / 252 : ℝ) ^ 19 *
        (1 + (779 / 1000 : ℝ) + (779 / 1000 : ℝ) ^ 2 / 2 + (779 / 1000 : ℝ) ^ 3 / 6 +
          (779 / 1000 : ℝ) ^ 4 / 24) := by
    norm_num only
  have ha : (32 : ℝ) * 12082601 ≤ Real.exp x0 := by
    have hlo := hn.trans (hprod.trans_eq hexp1)
    exact hlo.trans (Real.exp_le_exp.mpr hx1)
  have hscale : z ≤ (12082601 : ℝ) * (1 + (x - x0)) := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hnn : 0 ≤ 1 + (x - x0) := by linarith only [hx0]
  have hscaled := mul_le_mul_of_nonneg_right ha hnn
  have hl : 32 * z ≤ Real.exp x0 * (1 + (x - x0)) := by nlinarith only [hscale, hscaled]
  have hd := Real.add_one_le_exp (x - x0)
  have hrgt := mul_le_mul_of_nonneg_left hd (Real.exp_nonneg x0)
  have hexp : Real.exp x = Real.exp x0 * Real.exp (x - x0) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    32 * z ≤ Real.exp x0 * (1 + (x - x0)) := hl
    _ ≤ Real.exp x0 * Real.exp (x - x0) := by simpa only [add_comm] using hrgt
    _ = Real.exp x := hexp.symm

/-- At the 53-million double-log scale, exponent gap 401/1,000,000,000
absorbs the prime-counting loss 32z. The anchor is 21+253/1000. Sharper
finite exponential sums bound both exp(1) and the fractional exponential. -/
theorem thirty_two_mul_le_exp_gap_401_over_billion {z : ℝ} (hz : 53000000 ≤ z) :
    32 * z ≤ Real.exp (z * (401 / 1000000000 : ℝ)) := by
  let x : ℝ := z * (401 / 1000000000 : ℝ)
  let x0 : ℝ := 21253 / 1000
  have hx0 : x0 ≤ x := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hE1 : (685 / 252 : ℝ) ≤ Real.exp 1 := by
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1) 8
    have heq : (∑ k ∈ Finset.range 8, (1 : ℝ) ^ k / k.factorial) = 685 / 252 := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
        Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
    exact heq.symm.le.trans hsum
  have hEpow : (685 / 252 : ℝ) ^ 21 ≤ Real.exp 1 ^ 21 := pow_le_pow_left₀ (by norm_num only) hE1 21
  have hE21 : (685 / 252 : ℝ) ^ 21 ≤ Real.exp 21 := by
    calc
      _ ≤ Real.exp 1 ^ 21 := hEpow
      _ = Real.exp 21 := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num only
  have hrem :
    (1 + (253 / 1000 : ℝ) + (253 / 1000 : ℝ) ^ 2 / 2 + (253 / 1000 : ℝ) ^ 3 / 6) ≤
      Real.exp (253 / 1000 : ℝ) := by
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 253 / 1000) 4
    have heq :
      (∑ k ∈ Finset.range 4, (253 / 1000 : ℝ) ^ k / k.factorial) =
        1 + (253 / 1000 : ℝ) + (253 / 1000 : ℝ) ^ 2 / 2 + (253 / 1000 : ℝ) ^ 3 / 6 := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
        Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
    exact heq.symm.le.trans hsum
  have hprod :
    (685 / 252 : ℝ) ^ 21 *
        (1 + (253 / 1000 : ℝ) + (253 / 1000 : ℝ) ^ 2 / 2 + (253 / 1000 : ℝ) ^ 3 / 6) ≤
      Real.exp 21 * Real.exp (253 / 1000 : ℝ) :=
    mul_le_mul hE21 hrem (by norm_num only) (Real.exp_pos _).le
  have hexp0 : Real.exp 21 * Real.exp (253 / 1000 : ℝ) = Real.exp x0 := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [x0]
    norm_num only
  have hnum :
    (32 : ℝ) * 53000000 ≤
      (685 / 252 : ℝ) ^ 21 *
        (1 + (253 / 1000 : ℝ) + (253 / 1000 : ℝ) ^ 2 / 2 + (253 / 1000 : ℝ) ^ 3 / 6) := by
    norm_num only
  have hanchor : (32 : ℝ) * 53000000 ≤ Real.exp x0 := hnum.trans (hprod.trans_eq hexp0)
  have hscale : z ≤ (53000000 : ℝ) * (1 + (x - x0)) := by
    dsimp only [x, x0]
    nlinarith only [hz]
  have hnonneg : 0 ≤ 1 + (x - x0) := by linarith only [hx0]
  have hscaled := mul_le_mul_of_nonneg_right hanchor hnonneg
  have hleft : 32 * z ≤ Real.exp x0 * (1 + (x - x0)) := by nlinarith only [hscale, hscaled]
  have hdelta := Real.add_one_le_exp (x - x0)
  have hright := mul_le_mul_of_nonneg_left hdelta (Real.exp_nonneg x0)
  have hexp : Real.exp x = Real.exp x0 * Real.exp (x - x0) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    32 * z ≤ Real.exp x0 * (1 + (x - x0)) := hleft
    _ ≤ Real.exp x0 * Real.exp (x - x0) := by simpa only [add_comm] using hright
    _ = Real.exp x := hexp.symm

/-- The earlier 20-billion form is retained as a direct corollary of the
stronger 2-billion exponential absorption bound. -/
theorem thirty_two_mul_le_exp_gap_million_of_twenty_billion {z : ℝ} (hz : 20000000000 ≤ z) :
    32 * z ≤ Real.exp (z * (1 / 1000000 : ℝ)) :=
  thirty_two_mul_le_exp_gap_million_of_two_billion (le_trans (by norm_num only) hz)

/-- The prime-count and product-size budgets at scale 74/40 supply a smooth
cutoff with MR exponent 1850004/1000000 and product coefficient 999997/1000000. -/
theorem explicit_smooth_scale_74_40_gap {L : ℝ} (hL : 10 ^ 20 ≤ L) (hz : 10 ^ 11 ≤ Real.log L) :
    (999997 / 1000000 : ℝ) * (1850004 / 1000000) * L + (1850004 / 1000000 : ℝ) * Real.log L <
      (74 / 40) * L := by
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hz0 : 0 ≤ Real.log L := le_trans (by norm_num only) hz
  have hzpos : 0 < Real.log L :=
    Real.log_pos (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 10 ^ 20) hL)
  have hsq : (Real.log L) ^ 2 ≤ 2 * L := by
    have he := Real.quadratic_le_exp_of_nonneg hz0
    rw [Real.exp_log hLpos] at he
    nlinarith only [he, hz0]
  have hratio : Real.log L / L ≤ 2 / Real.log L := by
    apply (div_le_div_iff₀ hLpos hzpos).2
    nlinarith only [hsq]
  have hrecip : 1 / Real.log L ≤ 1 / (10 ^ 11 : ℝ) := by
    apply (div_le_div_iff₀ hzpos (by norm_num only : (0 : ℝ) < 10 ^ 11)).2
    nlinarith only [hz]
  have hsmall : Real.log L / L ≤ 2 / (10 ^ 11 : ℝ) := by
    calc
      _ ≤ 2 / Real.log L := hratio
      _ = 2 * (1 / Real.log L) := by ring
      _ ≤ 2 * (1 / (10 ^ 11 : ℝ)) := mul_le_mul_of_nonneg_left hrecip (by norm_num only)
      _ = _ := by ring
  have hscaled :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsmall (by norm_num only : (0 : ℝ) ≤ 1850004 / 1000000)) hLpos.le
  have hlog :
    (1850004 / 1000000 : ℝ) * Real.log L ≤ ((1850004 / 1000000 : ℝ) * (2 / 10 ^ 11)) * L := by
    calc
      _ = (1850004 / 1000000 : ℝ) * ((Real.log L / L) * L) := by rw [div_mul_cancel₀ _ hLpos.ne']
      _ = (1850004 / 1000000 : ℝ) * (Real.log L / L) * L := by ring
      _ ≤ _ := hscaled
  have hconst :
    (999997 / 1000000 : ℝ) * (1850004 / 1000000) + (1850004 / 1000000 : ℝ) * (2 / 10 ^ 11) <
      74 / 40 := by
    norm_num only
  have hmargin := mul_lt_mul_of_pos_right hconst hLpos
  nlinarith only [hlog, hmargin]

/-- The prime-count and product-size budgets at scale 70/38 supply a smooth
cutoff with MR exponent 184211/100000 and product coefficient 999997/1000000. -/
theorem explicit_smooth_scale_70_38_gap {L : ℝ} (hL : 10 ^ 20 ≤ L) (hz : 10 ^ 11 ≤ Real.log L) :
    (999997 / 1000000 : ℝ) * (184211 / 100000) * L + (184211 / 100000 : ℝ) * Real.log L <
      (70 / 38) * L := by
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hz0 : 0 ≤ Real.log L := le_trans (by norm_num only) hz
  have hzpos : 0 < Real.log L :=
    Real.log_pos (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 10 ^ 20) hL)
  have hsq : (Real.log L) ^ 2 ≤ 2 * L := by
    have he := Real.quadratic_le_exp_of_nonneg hz0
    rw [Real.exp_log hLpos] at he
    nlinarith only [he, hz0]
  have hratio : Real.log L / L ≤ 2 / Real.log L := by
    apply (div_le_div_iff₀ hLpos hzpos).2
    nlinarith only [hsq]
  have hrecip : 1 / Real.log L ≤ 1 / (10 ^ 11 : ℝ) := by
    apply (div_le_div_iff₀ hzpos (by norm_num only : (0 : ℝ) < 10 ^ 11)).2
    nlinarith only [hz]
  have hsmall : Real.log L / L ≤ 2 / (10 ^ 11 : ℝ) := by
    calc
      _ ≤ 2 / Real.log L := hratio
      _ = 2 * (1 / Real.log L) := by ring
      _ ≤ 2 * (1 / (10 ^ 11 : ℝ)) := mul_le_mul_of_nonneg_left hrecip (by norm_num only)
      _ = _ := by ring
  have hscaled :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsmall (by norm_num only : (0 : ℝ) ≤ 184211 / 100000)) hLpos.le
  have hlog : (184211 / 100000 : ℝ) * Real.log L ≤ ((184211 / 100000 : ℝ) * (2 / 10 ^ 11)) * L := by
    calc
      _ = (184211 / 100000 : ℝ) * ((Real.log L / L) * L) := by rw [div_mul_cancel₀ _ hLpos.ne']
      _ = (184211 / 100000 : ℝ) * (Real.log L / L) * L := by ring
      _ ≤ _ := hscaled
  have hconst :
    (999997 / 1000000 : ℝ) * (184211 / 100000) + (184211 / 100000 : ℝ) * (2 / 10 ^ 11) <
      70 / 38 := by
    norm_num only
  have hmargin := mul_lt_mul_of_pos_right hconst hLpos
  nlinarith only [hlog, hmargin]

/-- The prime-count and product-size budgets at scale 59/32 supply a smooth
cutoff with MR exponent 1843755/1000000 and product coefficient 999997/1000000.
The log-log input is 2 billion. -/
theorem explicit_smooth_scale_59_32_gap {L : ℝ} (hL : 10 ^ 20 ≤ L) (hz : 2000000000 ≤ Real.log L) :
    (999997 / 1000000 : ℝ) * (1843755 / 1000000) * L + (1843755 / 1000000 : ℝ) * Real.log L <
      (59 / 32) * L := by
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hz0 : 0 ≤ Real.log L := le_trans (by norm_num only) hz
  have hzpos : 0 < Real.log L :=
    Real.log_pos (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 10 ^ 20) hL)
  have hsq : (Real.log L) ^ 2 ≤ 2 * L := by
    have he := Real.quadratic_le_exp_of_nonneg hz0
    rw [Real.exp_log hLpos] at he
    nlinarith only [he, hz0]
  have hratio : Real.log L / L ≤ 2 / Real.log L := by
    apply (div_le_div_iff₀ hLpos hzpos).2
    nlinarith only [hsq]
  have hrecip : 1 / Real.log L ≤ 1 / (2000000000 : ℝ) := by
    apply (div_le_div_iff₀ hzpos (by norm_num only : (0 : ℝ) < 2000000000)).2
    nlinarith only [hz]
  have hsmall : Real.log L / L ≤ 2 / (2000000000 : ℝ) := by
    calc
      _ ≤ 2 / Real.log L := hratio
      _ = 2 * (1 / Real.log L) := by ring
      _ ≤ 2 * (1 / (2000000000 : ℝ)) := mul_le_mul_of_nonneg_left hrecip (by norm_num only)
      _ = _ := by ring
  have hscaled :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsmall (by norm_num only : (0 : ℝ) ≤ 1843755 / 1000000)) hLpos.le
  have hlog :
    (1843755 / 1000000 : ℝ) * Real.log L ≤ ((1843755 / 1000000 : ℝ) * (2 / 2000000000)) * L := by
    calc
      _ = (1843755 / 1000000 : ℝ) * ((Real.log L / L) * L) := by rw [div_mul_cancel₀ _ hLpos.ne']
      _ = (1843755 / 1000000 : ℝ) * (Real.log L / L) * L := by ring
      _ ≤ _ := hscaled
  have hconst :
    (999997 / 1000000 : ℝ) * (1843755 / 1000000) + (1843755 / 1000000 : ℝ) * (2 / 2000000000) <
      59 / 32 := by
    norm_num only
  have hmargin := mul_lt_mul_of_pos_right hconst hLpos
  nlinarith only [hlog, hmargin]

/-- At scale 19/10, the prime-count and product-size budgets supply smooth
inputs with MR exponent 1.900000016741 and coefficient 999999990522/1000000000000
from log-log threshold 3 billion. -/
theorem explicit_smooth_scale_19_10_gap {L : ℝ} (hL : 10 ^ 20 ≤ L) (hz : 3000000000 ≤ Real.log L) :
    (999999990522 / 1000000000000 : ℝ) * (1900000016741 / 1000000000000) * L +
        (1900000016741 / 1000000000000 : ℝ) * Real.log L <
      (19 / 10) * L := by
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hz0 : 0 ≤ Real.log L := le_trans (by norm_num only) hz
  have hzpos : 0 < Real.log L :=
    Real.log_pos (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 10 ^ 20) hL)
  have hsq : (Real.log L) ^ 2 ≤ 2 * L := by
    have he := Real.quadratic_le_exp_of_nonneg hz0
    rw [Real.exp_log hLpos] at he
    nlinarith only [he, hz0]
  have hratio : Real.log L / L ≤ 2 / Real.log L := by
    apply (div_le_div_iff₀ hLpos hzpos).2
    nlinarith only [hsq]
  have hrecip : 1 / Real.log L ≤ 1 / (3000000000 : ℝ) := by
    apply (div_le_div_iff₀ hzpos (by norm_num only : (0 : ℝ) < 3000000000)).2
    nlinarith only [hz]
  have hsmall : Real.log L / L ≤ 2 / (3000000000 : ℝ) := by
    calc
      _ ≤ 2 / Real.log L := hratio
      _ = 2 * (1 / Real.log L) := by ring
      _ ≤ 2 * (1 / (3000000000 : ℝ)) := mul_le_mul_of_nonneg_left hrecip (by norm_num only)
      _ = _ := by ring
  have hscaled :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsmall
        (by norm_num only : (0 : ℝ) ≤ 1900000016741 / 1000000000000))
      hLpos.le
  have hlog :
    (1900000016741 / 1000000000000 : ℝ) * Real.log L ≤
      ((1900000016741 / 1000000000000 : ℝ) * (2 / 3000000000)) * L := by
    calc
      _ = (1900000016741 / 1000000000000 : ℝ) * ((Real.log L / L) * L) := by
        rw [div_mul_cancel₀ _ hLpos.ne']
      _ = (1900000016741 / 1000000000000 : ℝ) * (Real.log L / L) * L := by ring
      _ ≤ _ := hscaled
  have hconst :
    (999999990522 / 1000000000000 : ℝ) * (1900000016741 / 1000000000000) +
        (1900000016741 / 1000000000000 : ℝ) * (2 / 3000000000) <
      19 / 10 := by
    norm_num only
  have hmargin := mul_lt_mul_of_pos_right hconst hLpos
  nlinarith only [hlog, hmargin]

/-- At scale 19/10, the stronger double-log threshold gives a smaller smooth
cutoff exponent and product coefficient. -/
theorem explicit_smooth_scale_19_10_gap_of_double_log_threshold_3084 {L : ℝ} (hL : 10 ^ 20 ≤ L)
    (hz : 3084000000 ≤ Real.log L) :
    (999999990558 / 1000000000000 : ℝ) * (1900000016707 / 1000000000000) * L +
        (1900000016707 / 1000000000000 : ℝ) * Real.log L <
      (19 / 10) * L := by
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hz0 : 0 ≤ Real.log L := le_trans (by norm_num only) hz
  have hzpos : 0 < Real.log L :=
    Real.log_pos (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 10 ^ 20) hL)
  have hsq : (Real.log L) ^ 2 ≤ 2 * L := by
    have he := Real.quadratic_le_exp_of_nonneg hz0
    rw [Real.exp_log hLpos] at he
    nlinarith only [he, hz0]
  have hratio : Real.log L / L ≤ 2 / Real.log L := by
    apply (div_le_div_iff₀ hLpos hzpos).2
    nlinarith only [hsq]
  have hrecip : 1 / Real.log L ≤ 1 / (3084000000 : ℝ) := by
    apply (div_le_div_iff₀ hzpos (by norm_num only : (0 : ℝ) < 3084000000)).2
    nlinarith only [hz]
  have hsmall : Real.log L / L ≤ 2 / (3084000000 : ℝ) := by
    calc
      _ ≤ 2 / Real.log L := hratio
      _ = 2 * (1 / Real.log L) := by ring
      _ ≤ 2 * (1 / (3084000000 : ℝ)) := mul_le_mul_of_nonneg_left hrecip (by norm_num only)
      _ = _ := by ring
  have hscaled :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsmall
        (by norm_num only : (0 : ℝ) ≤ 1900000016707 / 1000000000000))
      hLpos.le
  have hlog :
    (1900000016707 / 1000000000000 : ℝ) * Real.log L ≤
      ((1900000016707 / 1000000000000 : ℝ) * (2 / 3084000000)) * L := by
    calc
      _ = (1900000016707 / 1000000000000 : ℝ) * ((Real.log L / L) * L) := by
        rw [div_mul_cancel₀ _ hLpos.ne']
      _ = (1900000016707 / 1000000000000 : ℝ) * (Real.log L / L) * L := by ring
      _ ≤ _ := hscaled
  have hconst :
    (999999990558 / 1000000000000 : ℝ) * (1900000016707 / 1000000000000) +
        (1900000016707 / 1000000000000 : ℝ) * (2 / 3084000000) <
      19 / 10 := by
    norm_num only
  have hmargin := mul_lt_mul_of_pos_right hconst hLpos
  nlinarith only [hlog, hmargin]

/-- At scale 19/10, MR exponent 1.9000011 and product coefficient
0.99999934 satisfy the smooth-size inequality once log log L≥53,000,000. -/
theorem explicit_smooth_scale_19_10_gap_of_double_log_threshold_53m {L : ℝ} (hL : 10 ^ 12 ≤ L)
    (hz : 53000000 ≤ Real.log L) :
    (99999934 / 100000000 : ℝ) * (19000011 / 10000000) * L +
        (19000011 / 10000000 : ℝ) * Real.log L <
      (19 / 10) * L := by
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hz0 : 0 ≤ Real.log L := le_trans (by norm_num only) hz
  have hzpos : 0 < Real.log L :=
    Real.log_pos (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 10 ^ 12) hL)
  have hsq : (Real.log L) ^ 2 ≤ 2 * L := by
    have he := Real.quadratic_le_exp_of_nonneg hz0
    rw [Real.exp_log hLpos] at he
    nlinarith only [he, hz0]
  have hratio : Real.log L / L ≤ 2 / Real.log L := by
    apply (div_le_div_iff₀ hLpos hzpos).2
    nlinarith only [hsq]
  have hrecip : 1 / Real.log L ≤ 1 / (53000000 : ℝ) := by
    apply (div_le_div_iff₀ hzpos (by norm_num only : (0 : ℝ) < 53000000)).2
    nlinarith only [hz]
  have hsmall : Real.log L / L ≤ 2 / (53000000 : ℝ) := by
    calc
      _ ≤ 2 / Real.log L := hratio
      _ = 2 * (1 / Real.log L) := by ring
      _ ≤ 2 * (1 / (53000000 : ℝ)) := mul_le_mul_of_nonneg_left hrecip (by norm_num only)
      _ = _ := by ring
  have hscaled :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsmall (by norm_num only : (0 : ℝ) ≤ 19000011 / 10000000)) hLpos.le
  have hlog :
    (19000011 / 10000000 : ℝ) * Real.log L ≤ ((19000011 / 10000000 : ℝ) * (2 / 53000000)) * L := by
    calc
      _ = (19000011 / 10000000 : ℝ) * ((Real.log L / L) * L) := by rw [div_mul_cancel₀ _ hLpos.ne']
      _ = (19000011 / 10000000 : ℝ) * (Real.log L / L) * L := by ring
      _ ≤ _ := hscaled
  have hconst :
    (99999934 / 100000000 : ℝ) * (19000011 / 10000000) +
        (19000011 / 10000000 : ℝ) * (2 / 53000000) <
      19 / 10 := by
    norm_num only
  have hmargin := mul_lt_mul_of_pos_right hconst hLpos
  nlinarith only [hlog, hmargin]

/-- A double-log lower bound z0 and a rational product margin imply the
scale-19/10 smooth-size inequality. -/
theorem explicit_smooth_scale_19_10_gap_of_double_log_lower_bound {L A rho z0 : ℝ}
    (hL : 10 ^ 12 ≤ L) (hz : z0 ≤ Real.log L) (hz0 : 0 < z0) (hA : 0 ≤ A)
    (hmargin : rho * A + A * (2 / z0) < 19 / 10) :
    rho * A * L + A * Real.log L < (19 / 10) * L := by
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hzpos : 0 < Real.log L :=
    Real.log_pos (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 10 ^ 12) hL)
  have hsq : (Real.log L) ^ 2 ≤ 2 * L := by
    have he := Real.quadratic_le_exp_of_nonneg (le_trans hz0.le hz)
    rw [Real.exp_log hLpos] at he
    nlinarith only [he, hzpos.le]
  have hratio : Real.log L / L ≤ 2 / Real.log L := by
    apply (div_le_div_iff₀ hLpos hzpos).2
    nlinarith only [hsq]
  have hrecip : 1 / Real.log L ≤ 1 / z0 := by
    apply (div_le_div_iff₀ hzpos hz0).2
    nlinarith only [hz]
  have hsmall : Real.log L / L ≤ 2 / z0 := by
    calc
      _ ≤ 2 / Real.log L := hratio
      _ = 2 * (1 / Real.log L) := by ring
      _ ≤ 2 * (1 / z0) := mul_le_mul_of_nonneg_left hrecip (by norm_num only)
      _ = _ := by ring
  have hscaled := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hA) hLpos.le
  have hlog : A * Real.log L ≤ A * (2 / z0) * L := by
    calc
      _ = A * ((Real.log L / L) * L) := by rw [div_mul_cancel₀ _ hLpos.ne']
      _ = A * (Real.log L / L) * L := by ring
      _ ≤ _ := hscaled
  have hmargin' := mul_lt_mul_of_pos_right hmargin hLpos
  nlinarith only [hlog, hmargin']

/-- A double-log lower bound and a rational margin imply the smooth-size
inequality at any positive cutoff ratio. -/
theorem explicit_smooth_scale_gap_of_double_log_lower_bound {L A rho z0 kappa : ℝ}
    (hL : 10 ^ 12 ≤ L) (hz : z0 ≤ Real.log L) (hz0 : 0 < z0) (hA : 0 ≤ A)
    (hmargin : rho * A + A * (2 / z0) < kappa) : rho * A * L + A * Real.log L < kappa * L := by
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hzpos : 0 < Real.log L :=
    Real.log_pos (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 10 ^ 12) hL)
  have hsq : (Real.log L) ^ 2 ≤ 2 * L := by
    have he := Real.quadratic_le_exp_of_nonneg (le_trans hz0.le hz)
    rw [Real.exp_log hLpos] at he
    nlinarith only [he, hzpos.le]
  have hratio : Real.log L / L ≤ 2 / Real.log L := by
    apply (div_le_div_iff₀ hLpos hzpos).2
    nlinarith only [hsq]
  have hrecip : 1 / Real.log L ≤ 1 / z0 := by
    apply (div_le_div_iff₀ hzpos hz0).2
    nlinarith only [hz]
  have hsmall : Real.log L / L ≤ 2 / z0 := by
    calc
      _ ≤ 2 / Real.log L := hratio
      _ = 2 * (1 / Real.log L) := by ring
      _ ≤ 2 * (1 / z0) := mul_le_mul_of_nonneg_left hrecip (by norm_num only)
      _ = _ := by ring
  have hscaled := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hA) hLpos.le
  have hlog : A * Real.log L ≤ A * (2 / z0) * L := by
    calc
      _ = A * ((Real.log L / L) * L) := by rw [div_mul_cancel₀ _ hLpos.ne']
      _ = A * (Real.log L / L) * L := by ring
      _ ≤ _ := hscaled
  have hmargin' := mul_lt_mul_of_pos_right hmargin hLpos
  nlinarith only [hlog, hmargin']

/-- If log log L≥53,000,000, then L≥10^12. Use exp(x)≥x²/2 at
x=log L and avoid the stronger two-billion double-log hypothesis. -/
theorem twelve_pow_le_of_double_log_ge_fifty_three_million {L : ℝ} (hLpos : 0 < L)
    (hz : 53000000 ≤ Real.log L) : 10 ^ 12 ≤ L := by
  have hz0 : 0 ≤ Real.log L := le_trans (by norm_num only) hz
  have he := Real.quadratic_le_exp_of_nonneg hz0
  rw [Real.exp_log hLpos] at he
  nlinarith only [he, hz]

/-- A double-log threshold of 14,900,000 already forces L≥10^12.
Use the quadratic lower bound for exp(log L); this weaker threshold is enough
for the reduced 19/10 finite-fiber branch. -/
theorem twelve_pow_le_of_double_log_ge_fourteen_nine_million {L : ℝ} (hLpos : 0 < L)
    (hz : 14900000 ≤ Real.log L) : 10 ^ 12 ≤ L := by
  have hz0 : 0 ≤ Real.log L := le_trans (by norm_num only) hz
  have he := Real.quadratic_le_exp_of_nonneg hz0
  rw [Real.exp_log hLpos] at he
  nlinarith only [he, hz]

/-- A double-log threshold of 12,100,000 implies L≥10^12. Apply the
quadratic lower bound for exp(log L) at the smaller explicit threshold. -/
theorem twelve_pow_le_of_double_log_ge_twelve_million_one_hundred_thousand {L : ℝ} (hLpos : 0 < L)
    (hz : 12100000 ≤ Real.log L) : 10 ^ 12 ≤ L := by
  have hz0 : 0 ≤ Real.log L := le_trans (by norm_num only) hz
  have he := Real.quadratic_le_exp_of_nonneg hz0
  rw [Real.exp_log hLpos] at he
  nlinarith only [he, hz]

/-- A double-log lower bound of 12,082,601 implies L≥10^12. Apply the
quadratic lower bound for exp(log L) at the reduced 28/15 threshold. -/
theorem twelve_pow_le_of_double_log_ge_twelve_million_eighty_two_thousand_six_hundred_one {L : ℝ}
    (hLpos : 0 < L) (hz : 12082601 ≤ Real.log L) : 10 ^ 12 ≤ L := by
  have hz0 : 0 ≤ Real.log L := le_trans (by norm_num only) hz
  have he := Real.quadratic_le_exp_of_nonneg hz0
  rw [Real.exp_log hLpos] at he
  nlinarith only [he, hz]

/-- A fourth-degree exponential lower bound upgrades the 53-million
double-log threshold to the 10^20 input needed by the rational cutoff. -/
theorem twenty_pow_le_of_double_log_ge_fifty_three_million {L : ℝ} (hLpos : 0 < L)
    (hz : 53000000 ≤ Real.log L) : 10 ^ 20 ≤ L := by
  have hz0 : 0 ≤ Real.log L := le_trans (by norm_num only) hz
  have hx : 0 ≤ Real.log L / 2 := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have hsmall : (Real.log L) ^ 2 / 8 ≤ Real.exp (Real.log L / 2) := by nlinarith only [hq, hz0]
  have hsmallSq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (Real.log L) ^ 2 / 8) hsmall 2
  have hexp : Real.exp (Real.log L / 2) * Real.exp (Real.log L / 2) = Real.exp (Real.log L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hLrepr : Real.exp (Real.log L) = L := Real.exp_log hLpos
  have hpower : (Real.log L) ^ 4 / 64 ≤ L := by
    calc
      _ = ((Real.log L) ^ 2 / 8) ^ 2 := by ring
      _ ≤ (Real.exp (Real.log L / 2)) ^ 2 := hsmallSq
      _ = Real.exp (Real.log L) := by rw [pow_two, hexp]
      _ = L := hLrepr
  have hnum : (10 : ℝ) ^ 20 ≤ (53000000 : ℝ) ^ 4 / 64 := by norm_num only
  have hfour : (53000000 : ℝ) ^ 4 ≤ (Real.log L) ^ 4 :=
    pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 53000000) hz 4
  have hfrac : (53000000 : ℝ) ^ 4 / 64 ≤ (Real.log L) ^ 4 / 64 :=
    div_le_div_of_nonneg_right hfour (by norm_num only)
  exact hnum.trans (hfrac.trans hpower)

/-- At double-log scale 14,900,000, the input L already exceeds 10^20.
Use the fourth-degree exponential lower bound at log L. -/
theorem twenty_pow_le_of_double_log_ge_fourteen_nine_million {L : ℝ} (hL : 0 < L)
    (hz : 14900000 ≤ Real.log L) : 10 ^ 20 ≤ L := by
  have hz0 : 0 ≤ Real.log L := le_trans (by norm_num only) hz
  have hx : 0 ≤ Real.log L / 2 := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have hsmall : (Real.log L) ^ 2 / 8 ≤ Real.exp (Real.log L / 2) := by nlinarith only [hq, hz0]
  have hsmallSq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (Real.log L) ^ 2 / 8) hsmall 2
  have hexp : Real.exp (Real.log L / 2) * Real.exp (Real.log L / 2) = Real.exp (Real.log L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hLrepr : Real.exp (Real.log L) = L := Real.exp_log hL
  have hpower : (Real.log L) ^ 4 / 64 ≤ L := by
    calc
      _ = ((Real.log L) ^ 2 / 8) ^ 2 := by ring
      _ ≤ (Real.exp (Real.log L / 2)) ^ 2 := hsmallSq
      _ = Real.exp (Real.log L) := by rw [pow_two, hexp]
      _ = L := hLrepr
  have hnum : (10 : ℝ) ^ 20 ≤ (14900000 : ℝ) ^ 4 / 64 := by norm_num only
  have hfour : (14900000 : ℝ) ^ 4 ≤ (Real.log L) ^ 4 :=
    pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 14900000) hz 4
  have hfrac : (14900000 : ℝ) ^ 4 / 64 ≤ (Real.log L) ^ 4 / 64 :=
    div_le_div_of_nonneg_right hfour (by norm_num only)
  exact hnum.trans (hfrac.trans hpower)

/-- If log L≥2 billion, then L≥10^20 and the fixed rational product-size
margin at scale 147/80 is strict. Use a quadratic lower bound for exp(log L).
This controls the ceiling error in the number of prime factors. -/
theorem fixed_smooth_log_size_bounds {L : ℝ} (hL : 0 < L) (hz : 2000000000 ≤ Real.log L) :
    10 ^ 20 ≤ L ∧ (499 / 500 : ℝ) * (46 / 25) * L + (46 / 25) * Real.log L < (147 / 80) * L := by
  have hz0 : 0 ≤ Real.log L := le_trans (by norm_num only) hz
  have he := Real.quadratic_le_exp_of_nonneg hz0
  rw [Real.exp_log hL] at he
  have x_nonneg : 0 ≤ Real.log L / 2 := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg x_nonneg
  have hsmall : (Real.log L) ^ 2 / 8 ≤ Real.exp (Real.log L / 2) := by nlinarith only [hq, hz0]
  have hexp : Real.exp (Real.log L) = Real.exp (Real.log L / 2) * Real.exp (Real.log L / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hquartic : (Real.log L) ^ 4 / 64 ≤ Real.exp (Real.log L) := by
    rw [hexp]
    have hmul := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ (Real.log L) ^ 2 / 8)
    nlinarith only [hmul, hsmall]
  rw [Real.exp_log hL] at hquartic
  have hzsq : (2000000000 : ℝ) ^ 2 ≤ (Real.log L) ^ 2 := by
    have hprod :=
      mul_nonneg (sub_nonneg.mpr hz) (add_nonneg hz0 (by norm_num only : (0 : ℝ) ≤ 2000000000))
    nlinarith only [hprod]
  have hzfour : (2000000000 : ℝ) ^ 4 ≤ (Real.log L) ^ 4 := by
    have hmul := mul_le_mul hzsq hzsq (sq_nonneg (2000000000 : ℝ)) (sq_nonneg (Real.log L))
    nlinarith only [hmul]
  have hlarge : (10 : ℝ) ^ 20 ≤ (Real.log L) ^ 4 / 64 := by nlinarith only [hzfour]
  have hm := mul_nonneg hz0 (sub_nonneg.mpr hz)
  constructor
  · exact hlarge.trans hquartic
  · nlinarith only [he, hm, hz]

end PseudoPrime.Analysis
