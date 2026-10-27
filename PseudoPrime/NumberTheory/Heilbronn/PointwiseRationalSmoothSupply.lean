/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.SmoothPrimeProductCount
public import PseudoPrime.Analysis.RationalHeilbronnSmoothBudget

/-! # Pointwise smooth supply at a rational Heilbronn cutoff -/

public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For positive p,B,C,k and a, quantitative prime supply and logarithmic
product margins imply 256k≤p times the number of B-smooth inputs up to k.
Keep the natural smooth bound B and the count budget C as parameters.
This pointwise form supports explicit thresholds without asymptotic choices. -/
theorem smooth_count_at_rational_cutoff_of_log_bounds {p B C k a t : ℕ} {A b c beta : ℝ}
    (ha : 0 < a) (hp : 0 < p) (hB : 0 < B) (hC : 0 < C) (hk : 0 < k) (hL : 2 ≤ Real.log p)
    (hA : 0 < A) (hb : 1 < b) (hc : 0 < c) (hcb : beta < c * (b - 1))
    (hcL : 2 * c ≤ Real.log (Real.log p)) (hMp : 2 * (Real.log p) ^ b ≤ (B.primeCounting : ℝ))
    (hBL : (B : ℝ) ≤ (Real.log p) ^ A)
    (hgap : c * A * Real.log p + A * Real.log (Real.log p) < ((t : ℝ) / a) * Real.log p)
    (hlogC : Real.log C ≤ beta * Real.log p) (henv : 256 * k ≤ p * C) (hlo : p ^ t ≤ k ^ a) :
    256 * k ≤ p * (Nat.smoothNumbersUpTo k (B + 1)).card := by
  have hL1 : 1 < Real.log p := lt_of_lt_of_le (by norm_num only) hL
  obtain ⟨hs, hsL, hslo, hshi⟩ := Analysis.ceil_log_scale_bounds hc hL hcL
  have hsize : B ^ (Nat.ceil (c * Real.log p / Real.log (Real.log p))) < k :=
    Analysis.product_lt_rational_cutoff_of_log_scale ha hp hB hk hL1 hA hBL hshi hgap hlo
  have hbudget :
    C *
        (Nat.ceil (c * Real.log p / Real.log (Real.log p))) ^
          (Nat.ceil (c * Real.log p / Real.log (Real.log p))) <
      (B.primeCounting + 1 - Nat.ceil (c * Real.log p / Real.log (Real.log p))) ^
        (Nat.ceil (c * Real.log p / Real.log (Real.log p))) :=
    Analysis.subgroup_power_budget_of_log_scale hC hL1 hb hcb hs hsL hslo hMp hlogC
  have hchoose := NumberTheory.card_lt_choose_of_power_budget hbudget
  have hsmooth :=
    choose_le_smoothNumbersUpTo_card (S := B.primesLE) (fun q hq ↦ (Nat.mem_primesLE.mp hq).2)
      (fun q hq ↦ (Nat.mem_primesLE.mp hq).1) hsize.le
  rw [Nat.primesLE_card_eq_primeCounting] at hsmooth
  exact henv.trans (Nat.mul_le_mul_left p (hchoose.le.trans hsmooth))

/-- A prime-count and product-size budget at the fixed scale 125/68 supplies
the smooth inputs needed by every rational cutoff. The floor and logarithm
estimates remain pointwise; no unspecified starting threshold is chosen. -/
theorem fixed_smooth_count_at_rational_cutoff_of_bounds {p k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (hL : 2 ≤ Real.log p) (hB : 0 < Nat.floor ((Real.log p) ^ (1838239 / 1000000 : ℝ)))
    (hC : 0 < Nat.floor ((p : ℝ) ^ (8382354 / 10000000 : ℝ)))
    (hcL : 2 * (999997 / 1000000 : ℝ) ≤ Real.log (Real.log p))
    (hMp :
      2 * (Real.log p) ^ (1838238 / 1000000 : ℝ) ≤
        ((Nat.floor ((Real.log p) ^ (1838239 / 1000000 : ℝ))).primeCounting : ℝ))
    (hgap :
      (999997 / 1000000 : ℝ) * (1838239 / 1000000) * Real.log p +
          (1838239 / 1000000 : ℝ) * Real.log (Real.log p) <
        (125 / 68) * Real.log p)
    (henv : 256 * k ≤ p * Nat.floor ((p : ℝ) ^ (8382354 / 10000000 : ℝ))) (hlo : p ^ 125 ≤ k ^ 68) :
    256 * k ≤
      p *
        (Nat.smoothNumbersUpTo k
            (Nat.floor ((Real.log p) ^ (1838239 / 1000000 : ℝ)) + 1)).card := by
  have hlogC :=
    Real.log_le_log (Nat.cast_pos.mpr hC)
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) (8382354 / 10000000 : ℝ)))
  rw [Real.log_rpow (Nat.cast_pos.mpr hp) (8382354 / 10000000 : ℝ)] at hlogC
  exact
    smooth_count_at_rational_cutoff_of_log_bounds (a := 68) (t := 125) (by decide) hp hB hC hk hL
      (by norm_num only) (by norm_num only : (1 : ℝ) < 1838238 / 1000000)
      (by norm_num only : (0 : ℝ) < 999997 / 1000000)
      (by norm_num only : (8382354 / 10000000 : ℝ) < (999997 / 1000000) * (1838238 / 1000000 - 1))
      hcL hMp (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) _)) hgap hlogC henv hlo

/-- At scale 70/38, the displayed pointwise prime and floor bounds supply
the smooth inputs for every rational cutoff. -/
theorem fixed_smooth_count_at_rational_cutoff_74_40_of_bounds {p k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (hL : 2 ≤ Real.log p) (hB : 0 < Nat.floor ((Real.log p) ^ (1850004 / 1000000 : ℝ)))
    (hC : 0 < Nat.floor ((p : ℝ) ^ (8500002 / 10000000 : ℝ)))
    (hcL : 2 * (999997 / 1000000 : ℝ) ≤ Real.log (Real.log p))
    (hMp :
      2 * (Real.log p) ^ (1850003 / 1000000 : ℝ) ≤
        ((Nat.floor ((Real.log p) ^ (1850004 / 1000000 : ℝ))).primeCounting : ℝ))
    (hgap :
      (999997 / 1000000 : ℝ) * (1850004 / 1000000) * Real.log p +
          (1850004 / 1000000 : ℝ) * Real.log (Real.log p) <
        (74 / 40) * Real.log p)
    (henv : 256 * k ≤ p * Nat.floor ((p : ℝ) ^ (8500002 / 10000000 : ℝ))) (hlo : p ^ 74 ≤ k ^ 40) :
    256 * k ≤
      p *
        (Nat.smoothNumbersUpTo k
            (Nat.floor ((Real.log p) ^ (1850004 / 1000000 : ℝ)) + 1)).card := by
  have hlogC :=
    Real.log_le_log (Nat.cast_pos.mpr hC)
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) (8500002 / 10000000 : ℝ)))
  rw [Real.log_rpow (Nat.cast_pos.mpr hp) (8500002 / 10000000 : ℝ)] at hlogC
  exact
    smooth_count_at_rational_cutoff_of_log_bounds (a := 40) (t := 74) (by decide) hp hB hC hk hL
      (by norm_num only) (by norm_num only : (1 : ℝ) < 1850003 / 1000000)
      (by norm_num only : (0 : ℝ) < 999997 / 1000000)
      (by norm_num only : (8500002 / 10000000 : ℝ) < (999997 / 1000000) * (1850003 / 1000000 - 1))
      hcL hMp (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) _)) hgap hlogC henv hlo

/-- At the separate scale 74/40, the displayed pointwise prime and floor
bounds supply the smooth inputs for every rational cutoff. -/
theorem fixed_smooth_count_at_rational_cutoff_70_38_of_bounds {p k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (hL : 2 ≤ Real.log p) (hB : 0 < Nat.floor ((Real.log p) ^ (184211 / 100000 : ℝ)))
    (hC : 0 < Nat.floor ((p : ℝ) ^ (160000019 / 190000000 : ℝ)))
    (hcL : 2 * (999997 / 1000000 : ℝ) ≤ Real.log (Real.log p))
    (hMp :
      2 * (Real.log p) ^ (1842109 / 1000000 : ℝ) ≤
        ((Nat.floor ((Real.log p) ^ (184211 / 100000 : ℝ))).primeCounting : ℝ))
    (hgap :
      (999997 / 1000000 : ℝ) * (184211 / 100000) * Real.log p +
          (184211 / 100000 : ℝ) * Real.log (Real.log p) <
        (70 / 38) * Real.log p)
    (henv : 256 * k ≤ p * Nat.floor ((p : ℝ) ^ (160000019 / 190000000 : ℝ)))
    (hlo : p ^ 70 ≤ k ^ 38) :
    256 * k ≤
      p *
        (Nat.smoothNumbersUpTo k (Nat.floor ((Real.log p) ^ (184211 / 100000 : ℝ)) + 1)).card := by
  have hlogC :=
    Real.log_le_log (Nat.cast_pos.mpr hC)
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) (160000019 / 190000000 : ℝ)))
  rw [Real.log_rpow (Nat.cast_pos.mpr hp) (160000019 / 190000000 : ℝ)] at hlogC
  exact
    smooth_count_at_rational_cutoff_of_log_bounds (a := 38) (t := 70) (by decide) hp hB hC hk hL
      (by norm_num only) (by norm_num only : (1 : ℝ) < 1842109 / 1000000)
      (by norm_num only : (0 : ℝ) < 999997 / 1000000)
      (by norm_num only :
        (160000019 / 190000000 : ℝ) < (999997 / 1000000) * (1842109 / 1000000 - 1))
      hcL hMp (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) _)) hgap hlogC henv hlo

/-- At scale 59/32, pointwise prime and floor bounds supply the smooth
inputs for every rational cutoff. -/
theorem fixed_smooth_count_at_rational_cutoff_59_32_of_bounds {p k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (hL : 2 ≤ Real.log p) (hB : 0 < Nat.floor ((Real.log p) ^ (1843755 / 1000000 : ℝ)))
    (hC : 0 < Nat.floor ((p : ℝ) ^ (8437505 / 10000000 : ℝ)))
    (hcL : 2 * (999997 / 1000000 : ℝ) ≤ Real.log (Real.log p))
    (hMp :
      2 * (Real.log p) ^ (1843754 / 1000000 : ℝ) ≤
        ((Nat.floor ((Real.log p) ^ (1843755 / 1000000 : ℝ))).primeCounting : ℝ))
    (hgap :
      (999997 / 1000000 : ℝ) * (1843755 / 1000000) * Real.log p +
          (1843755 / 1000000 : ℝ) * Real.log (Real.log p) <
        (59 / 32) * Real.log p)
    (henv : 256 * k ≤ p * Nat.floor ((p : ℝ) ^ (8437505 / 10000000 : ℝ))) (hlo : p ^ 59 ≤ k ^ 32) :
    256 * k ≤
      p *
        (Nat.smoothNumbersUpTo k
            (Nat.floor ((Real.log p) ^ (1843755 / 1000000 : ℝ)) + 1)).card := by
  have hlogC :=
    Real.log_le_log (Nat.cast_pos.mpr hC)
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) (8437505 / 10000000 : ℝ)))
  rw [Real.log_rpow (Nat.cast_pos.mpr hp) (8437505 / 10000000 : ℝ)] at hlogC
  exact
    smooth_count_at_rational_cutoff_of_log_bounds (a := 32) (t := 59) (by decide) hp hB hC hk hL
      (by norm_num only) (by norm_num only : (1 : ℝ) < 1843754 / 1000000)
      (by norm_num only : (0 : ℝ) < 999997 / 1000000)
      (by norm_num only : (8437505 / 10000000 : ℝ) < (999997 / 1000000) * (1843754 / 1000000 - 1))
      hcL hMp (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) _)) hgap hlogC henv hlo

/-- At scale 19/10, the exponent 1.900000016707 and floor exponent 0.900000000000000001
supply smooth inputs for every rational cutoff. -/
theorem fixed_smooth_count_at_rational_cutoff_19_10_of_bounds {p k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (hL : 2 ≤ Real.log p) (hB : 0 < Nat.floor ((Real.log p) ^ (1900000016707 / 1000000000000 : ℝ)))
    (hC : 0 < Nat.floor ((p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ)))
    (hcL : 2 * (999999990558 / 1000000000000 : ℝ) ≤ Real.log (Real.log p))
    (hMp :
      2 * (Real.log p) ^ (1900000008498 / 1000000000000 : ℝ) ≤
        ((Nat.floor ((Real.log p) ^ (1900000016707 / 1000000000000 : ℝ))).primeCounting : ℝ))
    (hgap :
      (999999990558 / 1000000000000 : ℝ) * (1900000016707 / 1000000000000) * Real.log p +
          (1900000016707 / 1000000000000 : ℝ) * Real.log (Real.log p) <
        (19 / 10) * Real.log p)
    (henv : 256 * k ≤ p * Nat.floor ((p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ)))
    (hlo : p ^ 19 ≤ k ^ 10) :
    256 * k ≤
      p *
        (Nat.smoothNumbersUpTo k
            (Nat.floor ((Real.log p) ^ (1900000016707 / 1000000000000 : ℝ)) + 1)).card := by
  have hlogC :=
    Real.log_le_log (Nat.cast_pos.mpr hC)
      (Nat.floor_le
        (Real.rpow_nonneg (Nat.cast_nonneg p) (900000000000000001 / 1000000000000000000 : ℝ)))
  rw [Real.log_rpow (Nat.cast_pos.mpr hp) (900000000000000001 / 1000000000000000000 : ℝ)] at hlogC
  exact
    smooth_count_at_rational_cutoff_of_log_bounds (a := 10) (t := 19) (by decide) hp hB hC hk hL
      (by norm_num only) (by norm_num only : (1 : ℝ) < 1900000008498 / 1000000000000)
      (by norm_num only : (0 : ℝ) < 999999990558 / 1000000000000)
      (by norm_num only :
        (900000000000000001 / 1000000000000000000 : ℝ) <
          (999999990558 / 1000000000000) * (1900000008498 / 1000000000000 - 1))
      hcL hMp (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) _)) hgap hlogC henv hlo

end PseudoPrime.NumberTheory.Heilbronn
