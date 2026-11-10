/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 23 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 1154. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell23Rows : List Target028GeneralWeightRow :=
  [⟨1154, 2, 9, 6355, 6360, 9704, 1415, 61038, 30843⟩,
    ⟨1154, 3, 9, 5950, 5955, 9267, 1733, 94491, 30952⟩,
    ⟨1154, 4, 8, 5662, 5667, 8956, 2000, 128961, 30856⟩,
    ⟨1154, 5, 8, 5439, 5444, 8715, 2237, 164105, 30629⟩,
    ⟨1154, 7, 7, 5103, 5108, 8352, 2646, 235924, 30092⟩,
    ⟨1154, 8, 7, 4969, 4974, 8207, 2829, 272737, 29812⟩,
    ⟨1154, 9, 7, 4851, 4856, 8080, 3000, 309671, 29516⟩,
    ⟨1154, 33, 5, 3552, 3557, 6677, 5745, 1259550, 24140⟩,
    ⟨1154, 56, 4, 3023, 3028, 6106, 7484, 2229450, 20964⟩,
    ⟨1154, 79, 4, 2679, 2684, 5734, 8889, 3234114, 18700⟩,
    ⟨1154, 102, 4, 2424, 2429, 5459, 10100, 4257811, 16936⟩,
    ⟨1154, 125, 3, 2220, 2225, 5238, 11181, 5310867, 15527⟩,
    ⟨1154, 148, 3, 2051, 2056, 5056, 12166, 6370992, 14334⟩,
    ⟨1154, 171, 3, 1907, 1912, 4900, 13077, 7446583, 13330⟩,
    ⟨1154, 194, 3, 1781, 1786, 4764, 13929, 8531415, 12452⟩,
    ⟨1154, 217, 2, 1669, 1674, 4643, 14731, 9628767, 11683⟩,
    ⟨1154, 240, 2, 1568, 1573, 4534, 15492, 10737639, 10999⟩,
    ⟨1154, 263, 2, 1476, 1481, 4435, 16218, 11855065, 10382⟩,
    ⟨1154, 286, 2, 1392, 1397, 4344, 16912, 12984486, 9832⟩,
    ⟨1154, 309, 2, 1315, 1320, 4261, 17579, 14108187, 9330⟩,
    ⟨1154, 332, 2, 1243, 1248, 4183, 18221, 15252680, 8874⟩,
    ⟨1154, 355, 2, 1176, 1181, 4111, 18842, 16391374, 8451⟩,
    ⟨1154, 378, 2, 1114, 1119, 4044, 19443, 17527223, 8066⟩,
    ⟨1154, 401, 2, 1055, 1060, 3980, 20025, 18685639, 7711⟩,
    ⟨1154, 424, 1, 999, 1004, 3920, 20592, 19841094, 7374⟩,
    ⟨1154, 447, 1, 946, 951, 3863, 21143, 21004890, 7063⟩,
    ⟨1154, 470, 1, 896, 901, 3809, 21680, 22170338, 6776⟩,
    ⟨1154, 493, 1, 848, 853, 3757, 22204, 23353696, 6507⟩,
    ⟨1154, 516, 1, 802, 807, 3707, 22716, 24551066, 6255⟩,
    ⟨1154, 539, 1, 759, 764, 3661, 23217, 25706793, 6016⟩,
    ⟨1154, 562, 1, 717, 722, 3615, 23707, 26916925, 5795⟩,
    ⟨1154, 585, 1, 677, 682, 3572, 24187, 28099598, 5583⟩,
    ⟨1154, 608, 1, 638, 643, 3530, 24658, 29304915, 5382⟩,
    ⟨1154, 631, 1, 601, 606, 3490, 25120, 30500872, 5194⟩,
    ⟨1154, 654, 1, 565, 570, 3451, 25574, 31713906, 5015⟩,
    ⟨1154, 677, 1, 531, 536, 3414, 26020, 32909299, 4848⟩,
    ⟨1154, 700, 1, 497, 502, 3378, 26458, 34115617, 4682⟩,
    ⟨1154, 723, 1, 465, 470, 3343, 26889, 35330806, 4532⟩,
    ⟨1154, 746, 1, 434, 439, 3310, 27314, 36516173, 4384⟩,
    ⟨1154, 769, 1, 403, 408, 3276, 27731, 37779071, 4246⟩,
    ⟨1154, 792, 1, 374, 379, 3245, 28143, 38968564, 4113⟩,
    ⟨1154, 815, 1, 345, 350, 3213, 28549, 40235724, 3987⟩,
    ⟨1154, 838, 0, 317, 322, 3183, 28949, 41461085, 3865⟩,
    ⟨1154, 861, 0, 290, 295, 3154, 29343, 42681060, 3748⟩,
    ⟨1154, 884, 0, 264, 269, 3126, 29733, 43893018, 3637⟩,
    ⟨1154, 907, 0, 238, 243, 3098, 30117, 45139390, 3530⟩,
    ⟨1154, 930, 0, 213, 218, 3071, 30496, 46374756, 3427⟩,
    ⟨1154, 953, 0, 189, 194, 3045, 30871, 47596311, 3331⟩,
    ⟨1154, 976, 0, 165, 170, 3019, 31241, 48850043, 3236⟩,
    ⟨1154, 999, 0, 142, 147, 2994, 31607, 50086688, 3147⟩,
    ⟨1154, 1022, 0, 119, 124, 2969, 31969, 51354639, 3059⟩,
    ⟨1154, 1045, 0, 97, 102, 2946, 32327, 52549483, 2974⟩,
    ⟨1154, 1068, 0, 75, 80, 2922, 32681, 53825927, 2893⟩,
    ⟨1154, 1091, 0, 54, 59, 2899, 33031, 55078270, 2817⟩,
    ⟨1154, 1114, 0, 33, 38, 2877, 33377, 56303419, 2740⟩,
    ⟨1154, 1137, 0, 12, 17, 2854, 33720, 57613405, 2667⟩,
    ⟨1154, 1154, 0, -2, 2, 2838, 33971, 58542634, 2619⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell23_rows_check : ∀ r ∈ target028Cell23Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell23Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 1154)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell23RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell23Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨1154, 1154, 0, -2, 2, 2838, 33971, 58542634, 2619⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell23Weight (n : ℕ) : ℚ :=
  ((target028Cell23RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell23_select :
    ∀ n ∈ target028Cell23Prefix,
      1 ≤ n ∧
        target028Cell23RowFor n ∈ target028Cell23Rows ∧
        n ≤ (target028Cell23RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell23RowFor n).b) ∧ (target028Cell23RowFor n).cut = 1154 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell23_sum_check :
    (43481 / 5000 : ℚ) <
      ∑ n ∈ target028Cell23Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell23Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell23_principal :
    (43481 / 5000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(1154 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 1154 n).re := by
  have hs : target028Cell23Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell23Prefix ⊆ Finset.Ioc 0 ⌊(1154 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell23_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell23Prefix, 0 ≤ target028Cell23Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell23Prefix, (target028Cell23Weight n : ℝ) ≤ refinedScaledWeight 1154 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell23_select n hn
    have hcheck := target028_cell23_rows_check (target028Cell23RowFor n) hm
    have hrow := (target028Cell23RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell23RowFor n).b ≤ 1154 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 1154 (target028Cell23RowFor n).b ≤ refinedScaledWeight 1154 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 1154) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell23Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 1154) target028Cell23Prefix
      target028EulerData2701 target028Cell23Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((43481 / 5000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell23Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell23Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell23_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell23_budget :
    target028MomentBudget 1154 (66225 / 1000) ≤ 4 * (43481 / 5000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1154 10 32 0 (4407 / 625) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1154 0 (492969 / 1000000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 1154 ≤ (4407 / 625 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (1154 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (492969 / 1000000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (33969 / 1000 : ℝ) ≤ Real.sqrt 1154 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 1154 ≤ (8493 / 250 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 1154) (U := 66225 / 1000) (L := 4407 / 625) (P :=
      492969 / 1000000000) (s := 33969 / 1000) (t := 8493 / 250) (by norm_num only)
      (by norm_num only) hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell23_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (64225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 66225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1154 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 1154) (U := 66225 / 1000) (S := 43481 / 5000) (by norm_num only) hU hcut
      (le_of_lt target028_cell23_principal) target028_cell23_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
