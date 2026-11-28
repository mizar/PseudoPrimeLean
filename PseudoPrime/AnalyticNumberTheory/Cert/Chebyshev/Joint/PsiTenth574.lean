/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Psi70Window
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin3500To41539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Band3500
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch41539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch46539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch51539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch56539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch61539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch66539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch71539

/-! # One-sided Chebyshev estimate for the section 62 square cutoffs -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def start : Edge :=
  ⟨76539, 76516825709496550, 76517511241989268, 318170025089659, 318173836614825⟩

private def mid : Edge :=
  ⟨81219, 81274986802745718, 81275723384818501, 340448479726655, 340452523982820⟩

private def stop : Edge :=
  ⟨82379, 82462768519475473, 82463519120078846, 340448479726655, 340452523982820⟩

private theorem reach :
    Segment Valid (fun x ↦ x - (1 : ℕ) / (3 : ℝ) * Real.sqrt x ≤ Chebyshev.psi x) start mid := by
  apply
    psiLower_segment (u := 1) (by decide : 0 < 3) (a := 76539) (b := 81219) (k := 468) (by decide)
      (by decide) (by decide)
  decide +kernel

private theorem window :
    Segment Valid (fun x ↦ x - (1 : ℕ) / (10 : ℝ) * Real.sqrt x ≤ Chebyshev.psi x) mid stop := by
  apply
    psiLower_segment (u := 1) (by decide : 0 < 10) (a := 81219) (b := 82379) (k := 116) (by decide)
      (by decide) (by decide)
  decide +kernel

/-- On the half-open interval from 81219 to 82379 the one-sided psi error is
at most one tenth of the square root, by replaying 116 ten-integer cells. -/
theorem psi_tenth_window_574 {x : ℝ} (hl : 81219 ≤ x) (hu : x < 82379) :
    x - 1 / 10 * Real.sqrt x ≤ Chebyshev.psi x := by
  have h := (joined3500To41539 prefix3500.1).1
  have h1 := (batch51539 (batch46539 (batch41539 h).1).1).1
  have h2 := (batch71539 (batch66539 (batch61539 (batch56539 h1).1).1).1).1
  simpa only [Nat.cast_one] using (window (reach h2).1).2 x hl hu

private def radiusStart : Edge :=
  ⟨82369, 82451449506539321, 82452200091853414, 340448479726655, 340452523982820⟩

private def radiusStop : Edge :=
  ⟨82949, 83017568003310815, 83018320668164063, 340448479726655, 340452523982820⟩

private theorem radiusStart_valid : Valid radiusStart := by
  have h := (joined3500To41539 prefix3500.1).1
  have h1 := (batch51539 (batch46539 (batch41539 h).1).1).1
  have h2 := (batch71539 (batch66539 (batch61539 (batch56539 h1).1).1).1).1
  have ha :=
    psiLower_segment (s := mid) (t := radiusStart) (u := 1) (by decide : 0 < 10) (a := 81219) (b :=
      82369) (k := 115) (by decide) (by decide) (by decide) (by decide +kernel)
  exact (ha (reach h2).1).1

private theorem radius_segment :
    Segment Valid (fun x ↦ x - ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) * Real.sqrt x ≤ Chebyshev.psi x)
      radiusStart radiusStop := by
  exact
    psiLower_segment (s := radiusStart) (t := radiusStop) (u := 0) (by decide : 0 < 1) (a := 82369)
      (b := 82949) (k := 58) (by decide) (by decide) (by decide) (by decide +kernel)

/-- On every real point of [287²,82949), Chebyshev psi is at least the argument.
The lower walk checks zero error on 58 ten-integer cells after the certified prefix. -/
theorem psi_ge_self_window_576 {x : ℝ} (hl : 82369 ≤ x) (hu : x < 82949) : x ≤ Chebyshev.psi x := by
  simpa only [Nat.cast_zero, zero_div, zero_mul, sub_zero] using
    (radius_segment radiusStart_valid).2 x hl hu

private def radius289 : Edge :=
  ⟨83529, 83575548464705682, 83576307626858963, 343281693070707, 343285737326877⟩

private def radius292 : Edge :=
  ⟨85269, 85288410826266187, 85289183276214559, 343281693070707, 343285737326877⟩

private theorem next_segment :
    Segment Valid (fun x ↦ x - ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) * Real.sqrt x ≤ Chebyshev.psi x)
      radiusStop radius289 := by
  exact
    psiLower_segment (s := radiusStop) (t := radius289) (u := 0) (by decide : 0 < 1) (a := 82949)
      (b := 83529) (k := 58) (by decide) (by decide) (by decide) (by decide +kernel)

/-- Across the first section 94 interval the cutoff psi error is nonnegative,
including both square endpoints 288² and 289². -/
theorem psi_ge_self_window_578 {x : ℝ} (hl : 82369 ≤ x) (hu : x < 83529) : x ≤ Chebyshev.psi x := by
  by_cases h : x < 82949
  · exact psi_ge_self_window_576 hl h
  simpa only [Nat.cast_zero, zero_div, zero_mul, sub_zero] using
    (next_segment (radius_segment radiusStart_valid).1).2 x (le_of_not_gt h) hu

/-- Through the second section 94 interval a three-twenty-fifths lower error
covers every real argument up to and including 292². -/
theorem psi_lower_window_584 {x : ℝ} (hl : 82369 ≤ x) (hu : x < 85269) :
    x - 3 / 25 * Real.sqrt x ≤ Chebyshev.psi x := by
  by_cases h : x < 83529
  · exact
      (sub_le_self _ (mul_nonneg (by norm_num only) (Real.sqrt_nonneg _))).trans
        (psi_ge_self_window_578 hl h)
  have hs :=
    psiLower_segment (s := radius289) (t := radius292) (u := 3) (by decide : 0 < 25) (a := 83529)
      (b := 85269) (k := 174) (by decide) (by decide) (by decide) (by decide +kernel)
  exact (hs (next_segment (radius_segment radiusStart_valid).1).1).2 x (le_of_not_gt h) hu

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
