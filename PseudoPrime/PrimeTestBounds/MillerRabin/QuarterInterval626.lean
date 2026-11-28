/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInterval600
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMain570
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSignedBoundary570
import all PseudoPrime.Analysis.LogTaylorBounds
import all PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Euler bounds at radii 313 through 316 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At radius 313 the full Euler term satisfies the endpoint bound in (107.14). -/
theorem section107_euler_313 :
    section99Conductor 313 + 4 * positiveTail570 (313 ^ 2) ≤ 3.78087 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 313) (j := 8) (n := 32) (lo := 5) (hi :=
        5746203194 / 1000000000) (by decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 313) (p := 26) (d := 25)
        (lo := 0) (hi := 2538831564 / 1000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Nat.cast_ofNat, neg_div] at hl hp
  have hc := quarter_conductor_box (by norm_num only : (1 : ℝ) ≤ 313) hl hp
  have hz :=
    (Analysis.rationalLogIntervalCheck_sound (N := 97969) (j := 16) (n := 48) (lo := 11) (hi :=
        1149240640 / 100000000) (by decide +kernel)).2
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 97969) (p := 13) (d :=
        25) (lo := 0) (hi := 2538831563498 / 1000000000000000) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 97969) (p := 51) (d :=
        50) (lo := 0) (hi := 8111282951 / 1000000000000000) (by decide +kernel)).2
  have hb :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 97969) (p := 38) (d :=
        25) (lo := 0) (hi := 25914643 / 1000000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hz hm he hb
  have ht := quarter_tail_box (by norm_num only : (1 : ℝ) ≤ 97969) hz hm he hb
  rw [show (97969 : ℝ) = 313 ^ 2 by norm_num only, Real.sqrt_sq (by norm_num only)] at ht
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
    Nat.reduceAdd] at ht
  linarith only [hc, ht]

/-- At radius 314 the conductor and fourfold positive tail are at most 3.77598. -/
theorem section107_euler_314 :
    section99Conductor 314 + 4 * positiveTail570 (314 ^ 2) ≤ 3.77598 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 314) (j := 8) (n := 32) (lo := 5) (hi :=
        5749392988 / 1000000000) (by decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 314) (p := 26) (d := 25)
        (lo := 0) (hi := 2530423233 / 1000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Nat.cast_ofNat, neg_div] at hl hp
  have hc := quarter_conductor_box (by norm_num only : (1 : ℝ) ≤ 314) hl hp
  have hz :=
    (Analysis.rationalLogIntervalCheck_sound (N := 98596) (j := 16) (n := 48) (lo := 11) (hi :=
        1149878600 / 100000000) (by decide +kernel)).2
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 98596) (p := 13) (d :=
        25) (lo := 0) (hi := 2530423230771 / 1000000000000000) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 98596) (p := 51) (d :=
        50) (lo := 0) (hi := 8058672712 / 1000000000000000) (by decide +kernel)).2
  have hb :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 98596) (p := 38) (d :=
        25) (lo := 0) (hi := 25664565 / 1000000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hz hm he hb
  have ht := quarter_tail_box (by norm_num only : (1 : ℝ) ≤ 98596) hz hm he hb
  rw [show (98596 : ℝ) = 314 ^ 2 by norm_num only, Real.sqrt_sq (by norm_num only)] at ht
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
    Nat.reduceAdd] at ht
  linarith only [hc, ht]

/-- At radius 1568/5 the conductor and fourfold positive tail are at most 3.77798.
Enclose the squared radius between consecutive integers for the exponent bounds. -/
theorem quarter_euler_at_313_6 :
    section99Conductor (1568 / 5) + 4 * positiveTail570 ((1568 / 5) ^ 2) ≤ 3.77798 := by
  let r : ℝ := 1568 / 5
  let x : ℝ := r ^ 2
  have hr : 0 < r := by norm_num only [r]
  have hxl : (98344 : ℝ) ≤ x := by norm_num only [x, r]
  have hxu : x ≤ 98345 := by norm_num only [x, r]
  have hz :=
    (Analysis.rationalLogIntervalCheck_sound (N := 98345) (j := 16) (n := 48) (lo := 11) (hi :=
        1149623701 / 100000000) (by decide +kernel)).2
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 98344) (p := 13) (d :=
        25) (lo := 0) (hi := 2533792861831 / 1000000000000000) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 98344) (p := 51) (d :=
        50) (lo := 0) (hi := 8079736064 / 1000000000000000) (by decide +kernel)).2
  have hb :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 98344) (p := 38) (d :=
        25) (lo := 0) (hi := 25764593 / 1000000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hz hm he hb
  have hlog := (Real.log_le_log (sq_pos_of_pos hr) hxu).trans hz
  have hpow (t : ℝ) (ht : t ≤ 0) : x ^ t ≤ (98344 : ℝ) ^ t :=
    Real.rpow_le_rpow_of_nonpos (by norm_num only) hxl ht
  have hm' := (hpow (-(13 / 25)) (by norm_num only)).trans hm
  have ht :=
    quarter_tail_box (show 1 ≤ x from (by norm_num only : (1 : ℝ) ≤ 98344).trans hxl) hlog hm'
      ((hpow (-(51 / 50)) (by norm_num only)).trans he)
      ((hpow (-(38 / 25)) (by norm_num only)).trans hb)
  have heq : Real.log x = 2 * Real.log r := by
    unfold x
    rw [Real.log_pow, Nat.cast_ofNat]
  change Real.log x ≤ _ at hlog
  rw [heq] at hlog
  have hre : r ^ (-(26 / 25 : ℝ)) = x ^ (-(13 / 25 : ℝ)) := by
    rw [Real.rpow_def_of_pos hr, Real.rpow_def_of_pos (sq_pos_of_pos hr), heq]
    congr 1
    ring
  have hc :=
    quarter_conductor_box (show 1 ≤ r by norm_num only [r])
      (show Real.log r ≤ 1149623701 / 200000000 by linarith only [hlog]) (hre ▸ hm')
  change section99Conductor r + 4 * positiveTail570 x ≤ _
  rw [show Real.sqrt x = r from Real.sqrt_sq hr.le] at ht
  norm_num only [r, Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
    Nat.reduceAdd] at hc ht
  unfold r
  linarith only [hc, ht]

/-- At radius 6289/20 the conductor and fourfold positive tail are at most 3.77381.
Enclose the squared radius between consecutive integers for the exponent bounds. -/
theorem quarter_euler_at_314_45 :
    section99Conductor (6289 / 20) + 4 * positiveTail570 ((6289 / 20) ^ 2) ≤ 3.77381 := by
  let r : ℝ := 6289 / 20
  let x : ℝ := r ^ 2
  have hr : 0 < r := by norm_num only [r]
  have hxl : (98878 : ℝ) ≤ x := by norm_num only [x, r]
  have hxu : x ≤ 98879 := by norm_num only [x, r]
  have hz :=
    (Analysis.rationalLogIntervalCheck_sound (N := 98879) (j := 16) (n := 48) (lo := 11) (hi :=
        1150165218 / 100000000) (by decide +kernel)).2
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 98878) (p := 13) (d :=
        25) (lo := 0) (hi := 2526667940367 / 1000000000000000) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 98878) (p := 51) (d :=
        50) (lo := 0) (hi := 8035230385 / 1000000000000000) (by decide +kernel)).2
  have hb :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 98878) (p := 38) (d :=
        25) (lo := 0) (hi := 25553391 / 1000000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hz hm he hb
  have hlog := (Real.log_le_log (sq_pos_of_pos hr) hxu).trans hz
  have hpow (t : ℝ) (ht : t ≤ 0) : x ^ t ≤ (98878 : ℝ) ^ t :=
    Real.rpow_le_rpow_of_nonpos (by norm_num only) hxl ht
  have hm' := (hpow (-(13 / 25)) (by norm_num only)).trans hm
  have ht :=
    quarter_tail_box (show 1 ≤ x from (by norm_num only : (1 : ℝ) ≤ 98878).trans hxl) hlog hm'
      ((hpow (-(51 / 50)) (by norm_num only)).trans he)
      ((hpow (-(38 / 25)) (by norm_num only)).trans hb)
  have heq : Real.log x = 2 * Real.log r := by
    unfold x
    rw [Real.log_pow, Nat.cast_ofNat]
  change Real.log x ≤ _ at hlog
  rw [heq] at hlog
  have hre : r ^ (-(26 / 25 : ℝ)) = x ^ (-(13 / 25 : ℝ)) := by
    rw [Real.rpow_def_of_pos hr, Real.rpow_def_of_pos (sq_pos_of_pos hr), heq]
    congr 1
    ring
  have hc :=
    quarter_conductor_box (show 1 ≤ r by norm_num only [r])
      (show Real.log r ≤ 1150165218 / 200000000 by linarith only [hlog]) (hre ▸ hm')
  change section99Conductor r + 4 * positiveTail570 x ≤ _
  rw [show Real.sqrt x = r from Real.sqrt_sq hr.le] at ht
  norm_num only [r, Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
    Nat.reduceAdd] at hc ht
  unfold r
  linarith only [hc, ht]

/-- At radius 315 the conductor and fourfold positive tail are at most 3.77108. -/
theorem section107_euler_315 :
    section99Conductor 315 + 4 * positiveTail570 (315 ^ 2) ≤ 3.77108 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 315) (j := 8) (n := 32) (lo := 5) (hi :=
        5752572641 / 1000000000) (by decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 315) (p := 26) (d := 25)
        (lo := 0) (hi := 2522069351 / 1000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Nat.cast_ofNat, neg_div] at hl hp
  have hc := quarter_conductor_box (by norm_num only : (1 : ℝ) ≤ 315) hl hp
  have hz :=
    (Analysis.rationalLogIntervalCheck_sound (N := 99225) (j := 16) (n := 48) (lo := 11) (hi :=
        1150514530 / 100000000) (by decide +kernel)).2
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 99225) (p := 13) (d :=
        25) (lo := 0) (hi := 2522069348543 / 1000000000000000) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 99225) (p := 51) (d :=
        50) (lo := 0) (hi := 8006569363 / 1000000000000000) (by decide +kernel)).2
  have hb :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 99225) (p := 38) (d :=
        25) (lo := 0) (hi := 25417683 / 1000000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hz hm he hb
  have ht := quarter_tail_box (by norm_num only : (1 : ℝ) ≤ 99225) hz hm he hb
  rw [show (99225 : ℝ) = 315 ^ 2 by norm_num only, Real.sqrt_sq (by norm_num only)] at ht
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
    Nat.reduceAdd] at ht
  linarith only [hc, ht]

/-- At radius 316 the conductor and fourfold positive tail are at most 3.76622. -/
theorem section107_euler_316 :
    section99Conductor 316 + 4 * positiveTail570 (316 ^ 2) ≤ 3.76622 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 316) (j := 8) (n := 32) (lo := 5) (hi :=
        5755742216 / 1000000000) (by decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 316) (p := 26) (d := 25)
        (lo := 0) (hi := 2513769396 / 1000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Nat.cast_ofNat, neg_div] at hl hp
  have hc := quarter_conductor_box (by norm_num only : (1 : ℝ) ≤ 316) hl hp
  have hz :=
    (Analysis.rationalLogIntervalCheck_sound (N := 99856) (j := 16) (n := 48) (lo := 11) (hi :=
        1151148445 / 100000000) (by decide +kernel)).2
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 99856) (p := 13) (d :=
        25) (lo := 0) (hi := 2513769393023 / 1000000000000000) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 99856) (p := 51) (d :=
        50) (lo := 0) (hi := 7954966436 / 1000000000000000) (by decide +kernel)).2
  have hb :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 99856) (p := 38) (d :=
        25) (lo := 0) (hi := 25173947 / 1000000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hz hm he hb
  have ht := quarter_tail_box (by norm_num only : (1 : ℝ) ≤ 99856) hz hm he hb
  rw [show (99856 : ℝ) = 316 ^ 2 by norm_num only, Real.sqrt_sq (by norm_num only)] at ht
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
    Nat.reduceAdd] at ht
  linarith only [hc, ht]

/-- The three section 117 intervals use the right endpoint cap and the
logarithmic derivative bound on the combined conductor and Euler tail. -/
theorem quarter_euler_envelope_632 {r : ℝ} (hr : r ∈ Set.Icc 314 316) :
    section99Conductor r + 4 * positiveTail570 (r ^ 2) ≤
      if r ≤ 6289 / 20 then 3.77381 + (2.04 * 3.77598 / 314) * (6289 / 20 - r)
      else
        if r ≤ 315 then 3.77108 + (2.04 * 3.77381 / (6289 / 20)) * (315 - r)
        else 3.76622 + (2.04 * 3.77108 / 315) * (316 - r) := by
  by_cases h : r ≤ 6289 / 20
  · rw [ite_eq_left h]
    exact
      quarter_euler_row (by norm_num only) ⟨hr.1, h⟩ (by norm_num only) section107_euler_314
        quarter_euler_at_314_45
  rw [ite_eq_right h]
  by_cases h' : r ≤ 315
  · rw [ite_eq_left h']
    exact
      quarter_euler_row (by norm_num only) ⟨le_of_not_ge h, h'⟩ (by norm_num only)
        quarter_euler_at_314_45 section107_euler_315
  rw [ite_eq_right h']
  exact
    quarter_euler_row (by norm_num only) ⟨le_of_not_ge h', hr.2⟩ (by norm_num only)
      section107_euler_315 section107_euler_316

end PseudoPrime.PrimeTestBounds.MillerRabin
