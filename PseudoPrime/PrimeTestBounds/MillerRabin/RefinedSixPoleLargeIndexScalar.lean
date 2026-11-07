/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleIndex

/-! # Scalar gaps for the width-24 high-index argument -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `L ≥ 1000`, `0 ≤ y ≤ 27`, the paper's inner gap is positive if the
radius is at least `(261/500)L` and its square root is bounded by the stated
linear majorant. Nonnegative products control the two terms involving `y`;
the remaining comparison is rational arithmetic. -/
theorem refined_inner_gap_small {L r t y : ℝ} (hL : 1000 ≤ L) (hy0 : 0 ≤ y) (hy : y ≤ 27)
    (hr : (261 / 500 : ℝ) * L ≤ r) (ht0 : 0 ≤ t) (ht : t ≤ (151 / 200 : ℝ) * (5 / 158) * L) :
    (96 - y) * L + 16000 + L / 1000 <
      (292 - 4 * y) * r - (19 / 30 : ℝ) * (444 - 6 * y) * t - 1600 := by
  have hA : 0 ≤ (292 - 4 * y) * (r - (261 / 500 : ℝ) * L) :=
    mul_nonneg (by linarith only [hy]) (by linarith only [hr])
  have hB : 0 ≤ y * t := mul_nonneg hy0 ht0
  have hC : 0 ≤ (27 - y) * L := mul_nonneg (by linarith only [hy]) (by linarith only [hL])
  nlinarith only [hA, hB, hC, ht, hL]

/-- For `L ≥ 10^6` and `0 ≤ y ≤ 48`, the paper's inner gap is positive under
the radius and square-root estimates. The same nonnegative-product argument
uses the wider logarithmic range and the stronger linear square-root bound. -/
theorem refined_inner_gap_large {L r t y : ℝ} (hL : 1000000 ≤ L) (hy0 : 0 ≤ y) (hy : y ≤ 48)
    (hr : (261 / 500 : ℝ) * L ≤ r) (ht0 : 0 ≤ t) (ht : t ≤ (151 / 200 : ℝ) / 1000 * L) :
    (96 - y) * L + 16000 + L / 1000 <
      (292 - 4 * y) * r - (19 / 30 : ℝ) * (444 - 6 * y) * t - 1600 := by
  have hA : 0 ≤ (292 - 4 * y) * (r - (261 / 500 : ℝ) * L) :=
    mul_nonneg (by linarith only [hy]) (by linarith only [hr])
  have hB : 0 ≤ y * t := mul_nonneg hy0 ht0
  have hC : 0 ≤ (48 - y) * L := mul_nonneg (by linarith only [hy]) (by linarith only [hL])
  nlinarith only [hA, hB, hC, ht, hL]

/-- For `L ≥ 10^10`, the paper's outer gap is positive under the stated radius
and square-root estimates. Exact rational arithmetic keeps the small positive
margin needed beyond logarithmic support. -/
theorem refined_outer_gap {L r t : ℝ} (hL : 10000000000 ≤ L) (hr : (261 / 500 : ℝ) * L ≤ r)
    (ht : t ≤ (151 / 200 : ℝ) / 100000 * L) : 48 * L + 16000 + L / 1000 < 92 * r - 2100 * t := by
  linarith only [hL, hr, ht]

/-- For a nonnegative allowance at most three, the positive paper root is at
most `(151/200) sqrt L` on `L ≥ 1000`. Compare squares using the existing
upper bound for the squared root. -/
theorem refined_root_sqrt_cap {L K : ℝ} (hL : 1000 ≤ L) (hK : 0 ≤ K) (hK3 : K ≤ 3) :
    refinedPaperRoot L K ≤ (151 / 200 : ℝ) * Real.sqrt L := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hs := Real.sq_sqrt hL0
  have hu := refined_root_upper hL hK hK3
  have hr := (refined_paper_root_positive L K).le
  have hm :=
    mul_le_mul_of_nonneg_right (show (57 / 100 : ℝ) ≤ (151 / 200 : ℝ) ^ 2 by norm_num only) hL0
  have hsq : refinedPaperRoot L K ^ 2 ≤ ((151 / 200 : ℝ) * Real.sqrt L) ^ 2 := by
    nlinarith only [hu, hm, hs]
  exact (sq_le_sq₀ hr (by positivity)).mp hsq

/-- The inner scalar gap holds at the paper root for `L ≥ 1000` when the
cutoff logarithm lies in `[0,27]`. The root bounds and a linear estimate for
`sqrt L` discharge the abstract radius hypotheses. -/
theorem refined_root_inner_gap_small {L K y : ℝ} (hL : 1000 ≤ L) (hK : 0 ≤ K) (hK3 : K ≤ 3)
    (hy0 : 0 ≤ y) (hy : y ≤ 27) :
    (96 - y) * L + 16000 + L / 1000 <
      (292 - 4 * y) * refinedPaperRoot L K ^ 2 -
        (19 / 30 : ℝ) * (444 - 6 * y) * refinedPaperRoot L K -
        1600 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hs : Real.sqrt L ≤ (5 / 158 : ℝ) * L := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith only [hL, sq_nonneg (L - 1000)]
  have hr := refined_root_lower hL0 hK
  have ht :=
    (refined_root_sqrt_cap hL hK hK3).trans
      (mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 151 / 200))
  exact
    refined_inner_gap_small hL hy0 hy hr (refined_paper_root_positive L K).le
      (by simpa only [mul_assoc] using ht)

/-- The inner scalar gap holds at the paper root for `L ≥ 10^6` and cutoff
logarithm in `[0,48]`. The sharper square-root estimate supplies the hypotheses
of the large-scale inner gap. -/
theorem refined_root_inner_gap_large {L K y : ℝ} (hL : 1000000 ≤ L) (hK : 0 ≤ K) (hK3 : K ≤ 3)
    (hy0 : 0 ≤ y) (hy : y ≤ 48) :
    (96 - y) * L + 16000 + L / 1000 <
      (292 - 4 * y) * refinedPaperRoot L K ^ 2 -
        (19 / 30 : ℝ) * (444 - 6 * y) * refinedPaperRoot L K -
        1600 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have h1000 : 1000 ≤ L := by linarith only [hL]
  have hs : Real.sqrt L ≤ L / 1000 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith only [hL, sq_nonneg (L - 1000000)]
  have hr := refined_root_lower hL0 hK
  have ht :=
    (refined_root_sqrt_cap h1000 hK hK3).trans
      (mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 151 / 200))
  apply refined_inner_gap_large hL hy0 hy hr (refined_paper_root_positive L K).le
  nlinarith only [ht]

/-- The outer scalar gap holds at the paper root for `L ≥ 10^10`. Apply the
root's linear square-root cap to the exact outer inequality. -/
theorem refined_root_outer_gap {L K : ℝ} (hL : 10000000000 ≤ L) (hK : 0 ≤ K) (hK3 : K ≤ 3) :
    48 * L + 16000 + L / 1000 < 92 * refinedPaperRoot L K ^ 2 - 2100 * refinedPaperRoot L K := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have h1000 : 1000 ≤ L := by linarith only [hL]
  have hs : Real.sqrt L ≤ L / 100000 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith only [hL, sq_nonneg (L - 10000000000)]
  have hr := refined_root_lower hL0 hK
  have ht :=
    (refined_root_sqrt_cap h1000 hK hK3).trans
      (mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 151 / 200))
  apply refined_outer_gap hL hr
  nlinarith only [ht]

/-- The principal cost in the width-24 argument is less than `hL/1000` when
`h ≥ 10^16`, `L ≥ 1000`, and the radius lies in the paper's linear interval.
Bound the square root and both reciprocals by elementary functions of the
radius, then compare the resulting rational coefficients. -/
theorem refined_large_index_cost {L r h : ℝ} (hL : 1000 ≤ L) (hrlo : (261 / 500 : ℝ) * L ≤ r)
    (hrhi : r ≤ (57 / 100 : ℝ) * L) (hh : 10000000000000000 ≤ h) :
    (130000000000 : ℝ) * (r + r⁻¹) + 500000000 * (Real.sqrt r + (Real.sqrt r)⁻¹) +
        2 * (130000000000 + 500000000) <
      h * L / 1000 := by
  have hr1 : (1 : ℝ) ≤ r := by linarith only [hL, hrlo]
  have hi : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
  have hs1 : (1 : ℝ) ≤ Real.sqrt r := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hr1]
  have hsi : (Real.sqrt r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
  have hsr : Real.sqrt r ≤ r := by
    apply (Real.sqrt_le_left (by linarith only [hr1])).mpr
    nlinarith only [hr1, sq_nonneg (r - 1)]
  have hm : 0 ≤ (h - 10000000000000000) * L :=
    mul_nonneg (by linarith only [hh]) (by linarith only [hL])
  nlinarith only [hL, hrhi, hi, hsi, hsr, hm]

/-- At the paper root, the explicit principal cost and the width-24 conductor
budget are strictly below the inner principal lower bound when `0 ≤ y ≤ 27`
and the index is at least `10^16`. This is the scalar contradiction needed
once the analytic width-24 comparison supplies its no-witness inequality. -/
theorem refined_root_inner_index_gap {L K y h : ℝ} (hL : 1000 ≤ L) (hK : 0 ≤ K) (hK3 : K ≤ 3)
    (hy0 : 0 ≤ y) (hy : y ≤ 27) (hh : 10000000000000000 ≤ h) :
    (130000000000 : ℝ) * (refinedPaperRoot L K ^ 2 + (refinedPaperRoot L K ^ 2)⁻¹) +
        500000000 * (refinedPaperRoot L K + (refinedPaperRoot L K)⁻¹) +
        2 * (130000000000 + 500000000) +
        (h - 1) * ((96 - y) * L + 16000) <
      h *
        ((292 - 4 * y) * refinedPaperRoot L K ^ 2 -
          (19 / 30 : ℝ) * (444 - 6 * y) * refinedPaperRoot L K -
          1600) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hrlo := refined_root_lower hL0 hK
  have hrhi := refined_root_upper hL hK hK3
  have hcost := refined_large_index_cost hL hrlo hrhi hh
  rw [Real.sqrt_sq (refined_paper_root_positive L K).le] at hcost
  have hgap := refined_root_inner_gap_small hL hK hK3 hy0 hy
  have hmul := mul_lt_mul_of_pos_left hgap (show 0 < h by linarith only [hh])
  have hbudget : 0 ≤ (96 - y) * L + 16000 := by
    have h := mul_nonneg (show (0 : ℝ) ≤ 96 - y by linarith only [hy]) hL0
    linarith only [h]
  nlinarith only [hcost, hmul, hbudget]

/-- At the paper root and `L ≥ 10^6`, the width-24 inner scalar comparison is
strict throughout `0 ≤ y ≤ 48` for indices at least `10^16`. Combine the
principal-cost bound with the large-scale inner gap. -/
theorem refined_root_inner_index_large {L K y h : ℝ} (hL : 1000000 ≤ L) (hK : 0 ≤ K) (hK3 : K ≤ 3)
    (hy0 : 0 ≤ y) (hy : y ≤ 48) (hh : 10000000000000000 ≤ h) :
    (130000000000 : ℝ) * (refinedPaperRoot L K ^ 2 + (refinedPaperRoot L K ^ 2)⁻¹) +
        500000000 * (refinedPaperRoot L K + (refinedPaperRoot L K)⁻¹) +
        2 * (130000000000 + 500000000) +
        (h - 1) * ((96 - y) * L + 16000) <
      h *
        ((292 - 4 * y) * refinedPaperRoot L K ^ 2 -
          (19 / 30 : ℝ) * (444 - 6 * y) * refinedPaperRoot L K -
          1600) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have h1000 : 1000 ≤ L := by linarith only [hL]
  have hrlo := refined_root_lower hL0 hK
  have hrhi := refined_root_upper h1000 hK hK3
  have hcost := refined_large_index_cost h1000 hrlo hrhi hh
  rw [Real.sqrt_sq (refined_paper_root_positive L K).le] at hcost
  have hgap := refined_root_inner_gap_large hL hK hK3 hy0 hy
  have hmul := mul_lt_mul_of_pos_left hgap (show 0 < h by linarith only [hh])
  have hbudget : 0 ≤ (96 - y) * L + 16000 := by
    have h := mul_nonneg (show (0 : ℝ) ≤ 96 - y by linarith only [hy]) hL0
    linarith only [h]
  nlinarith only [hcost, hmul, hbudget]

/-- At the paper root and `L ≥ 10^10`, the width-24 outer scalar comparison is
strict for indices at least `10^16`. Combine the principal-cost bound with the
outer principal lower bound. -/
theorem refined_root_outer_index_gap {L K h : ℝ} (hL : 10000000000 ≤ L) (hK : 0 ≤ K) (hK3 : K ≤ 3)
    (hh : 10000000000000000 ≤ h) :
    (130000000000 : ℝ) * (refinedPaperRoot L K ^ 2 + (refinedPaperRoot L K ^ 2)⁻¹) +
        500000000 * (refinedPaperRoot L K + (refinedPaperRoot L K)⁻¹) +
        2 * (130000000000 + 500000000) +
        (h - 1) * (48 * L + 16000) <
      h * (92 * refinedPaperRoot L K ^ 2 - 2100 * refinedPaperRoot L K) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have h1000 : 1000 ≤ L := by linarith only [hL]
  have hrlo := refined_root_lower hL0 hK
  have hrhi := refined_root_upper h1000 hK hK3
  have hcost := refined_large_index_cost h1000 hrlo hrhi hh
  rw [Real.sqrt_sq (refined_paper_root_positive L K).le] at hcost
  have hgap := refined_root_outer_gap hL hK hK3
  have hmul := mul_lt_mul_of_pos_left hgap (show 0 < h by linarith only [hh])
  nlinarith only [hcost, hmul, hL]

/-- For `1000 ≤ L ≤ 10^6`, the logarithm of the paper cutoff lies in `[0,27]`
for every allowance in `[0,3]`. The root bounds control the cutoff and a finite
rational logarithm certificate supplies the upper endpoint. -/
theorem refined_cutoff_log_small {L K : ℝ} (hL : 1000 ≤ L) (hU : L ≤ 1000000) (hK : 0 ≤ K)
    (hK3 : K ≤ 3) :
    0 ≤ Real.log (refinedPaperBound L K) ∧ Real.log (refinedPaperBound L K) ≤ 27 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hrlo := refined_root_lower hL0 hK
  have hrhi := refined_root_upper hL hK hK3
  have hsq0 : 0 ≤ refinedPaperRoot L K ^ 2 := sq_nonneg _
  have hsqlo : (1 : ℝ) ≤ refinedPaperRoot L K ^ 2 := by linarith only [hrlo, hL]
  have hsqhi : refinedPaperRoot L K ^ 2 ≤ 570000 := by linarith only [hrhi, hU]
  have hpowlo := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num only) hsqlo 2
  have hpowhi := pow_le_pow_left₀ hsq0 hsqhi 2
  have hB1 : (1 : ℝ) ≤ refinedPaperBound L K := by
    dsimp only [refinedPaperBound]
    nlinarith only [hpowlo]
  have hBhi : refinedPaperBound L K ≤ 324900000000 := by
    dsimp only [refinedPaperBound]
    nlinarith only [hpowhi]
  have hc : Analysis.rationalLogIntervalCheck 324900000000 39 64 0 27 = true := by decide +kernel
  have hl := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat] at hl
  exact ⟨Real.log_nonneg hB1, (Real.log_le_log (by linarith only [hB1]) hBhi).trans hl⟩

/-- For `1000 ≤ L ≤ 10^6`, the width-24 inner scalar gap holds at the actual
paper cutoff without a separate logarithm hypothesis. The certified cutoff
logarithm lies in `[0,27]`, so the inner index gap applies directly. -/
theorem refined_cutoff_inner_index_gap {L K h : ℝ} (hL : 1000 ≤ L) (hU : L ≤ 1000000) (hK : 0 ≤ K)
    (hK3 : K ≤ 3) (hh : 10000000000000000 ≤ h) :
    (130000000000 : ℝ) * (refinedPaperRoot L K ^ 2 + (refinedPaperRoot L K ^ 2)⁻¹) +
        500000000 * (refinedPaperRoot L K + (refinedPaperRoot L K)⁻¹) +
        2 * (130000000000 + 500000000) +
        (h - 1) * ((96 - Real.log (refinedPaperBound L K)) * L + 16000) <
      h *
        ((292 - 4 * Real.log (refinedPaperBound L K)) * refinedPaperRoot L K ^ 2 -
          (19 / 30 : ℝ) * (444 - 6 * Real.log (refinedPaperBound L K)) * refinedPaperRoot L K -
          1600) := by
  have hl := refined_cutoff_log_small hL hU hK hK3
  exact refined_root_inner_index_gap hL hK hK3 hl.1 hl.2 hh

/-- If the logarithm of the paper cutoff is at least `48`, then `L ≥ 10^10`.
Otherwise the root upper bound puts the cutoff below a fixed rational number
whose logarithm is certified to be at most `45`. -/
theorem refined_cutoff_outer_scale {L K : ℝ} (hL : 1000 ≤ L) (hK : 0 ≤ K) (hK3 : K ≤ 3)
    (hy : 48 ≤ Real.log (refinedPaperBound L K)) : 10000000000 ≤ L := by
  by_contra hn
  have hU : L ≤ 10000000000 := (lt_of_not_ge hn).le
  have hrhi := refined_root_upper hL hK hK3
  have hsq0 : 0 ≤ refinedPaperRoot L K ^ 2 := sq_nonneg _
  have hsqhi : refinedPaperRoot L K ^ 2 ≤ 5700000000 := by linarith only [hrhi, hU]
  have hpowhi := pow_le_pow_left₀ hsq0 hsqhi 2
  have hBhi : refinedPaperBound L K ≤ 32490000000000000000 := by
    dsimp only [refinedPaperBound]
    nlinarith only [hpowhi]
  have hB0 : 0 < refinedPaperBound L K := pow_pos (refined_paper_root_positive L K) 4
  have hc : Analysis.rationalLogIntervalCheck 32490000000000000000 65 64 0 45 = true := by
    decide +kernel
  have hl := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat] at hl
  have hupper := (Real.log_le_log hB0 hBhi).trans hl
  linarith only [hy, hupper]

/-- At a paper cutoff with logarithm at least `48`, the width-24 outer index
gap is strict. The cutoff-logarithm condition implies the scale required by
the previously proved outer scalar certificate. -/
theorem refined_cutoff_outer_index_gap {L K h : ℝ} (hL : 1000 ≤ L) (hK : 0 ≤ K) (hK3 : K ≤ 3)
    (hh : 10000000000000000 ≤ h) (hy : 48 ≤ Real.log (refinedPaperBound L K)) :
    (130000000000 : ℝ) * (refinedPaperRoot L K ^ 2 + (refinedPaperRoot L K ^ 2)⁻¹) +
        500000000 * (refinedPaperRoot L K + (refinedPaperRoot L K)⁻¹) +
        2 * (130000000000 + 500000000) +
        (h - 1) * (48 * L + 16000) <
      h * (92 * refinedPaperRoot L K ^ 2 - 2100 * refinedPaperRoot L K) := by
  exact refined_root_outer_index_gap (refined_cutoff_outer_scale hL hK hK3 hy) hK hK3 hh

/-- At a paper cutoff with logarithm at most `48`, the width-24 inner index
gap is strict for all `L ≥ 1000`. Split at `10^6` and use the certified
cutoff-logarithm bound in the lower range and the stronger square-root estimate
in the upper range. -/
theorem refined_cutoff_inner_index_all {L K h : ℝ} (hL : 1000 ≤ L) (hK : 0 ≤ K) (hK3 : K ≤ 3)
    (hh : 10000000000000000 ≤ h) (hy : Real.log (refinedPaperBound L K) ≤ 48) :
    (130000000000 : ℝ) * (refinedPaperRoot L K ^ 2 + (refinedPaperRoot L K ^ 2)⁻¹) +
        500000000 * (refinedPaperRoot L K + (refinedPaperRoot L K)⁻¹) +
        2 * (130000000000 + 500000000) +
        (h - 1) * ((96 - Real.log (refinedPaperBound L K)) * L + 16000) <
      h *
        ((292 - 4 * Real.log (refinedPaperBound L K)) * refinedPaperRoot L K ^ 2 -
          (19 / 30 : ℝ) * (444 - 6 * Real.log (refinedPaperBound L K)) * refinedPaperRoot L K -
          1600) := by
  by_cases hU : L ≤ 1000000
  · exact refined_cutoff_inner_index_gap hL hU hK hK3 hh
  · have hL0 : 0 ≤ L := by linarith only [hL]
    have hrlo := refined_root_lower hL0 hK
    have hsqlo : (1 : ℝ) ≤ refinedPaperRoot L K ^ 2 := by linarith only [hrlo, hL]
    have hpowlo := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num only) hsqlo 2
    have hB1 : (1 : ℝ) ≤ refinedPaperBound L K := by
      dsimp only [refinedPaperBound]
      nlinarith only [hpowlo]
    have hy0 := Real.log_nonneg hB1
    exact refined_root_inner_index_large (le_of_not_ge hU) hK hK3 hy0 hy hh

end PseudoPrime.PrimeTestBounds.MillerRabin
