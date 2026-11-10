/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral

/-! # Uniform analytic cell 20 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 949. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell20Rows : List Target028GeneralWeightRow :=
  [⟨949, 2, 9, 6160, 6165, 9494, 1415, 75302, 34095⟩,
    ⟨949, 3, 8, 5754, 5759, 9055, 1733, 116805, 34084⟩,
    ⟨949, 4, 8, 5467, 5472, 8745, 2000, 159255, 33828⟩,
    ⟨949, 5, 8, 5243, 5248, 8503, 2237, 202858, 33479⟩,
    ⟨949, 7, 7, 4907, 4912, 8140, 2646, 291637, 32714⟩,
    ⟨949, 8, 7, 4773, 4778, 7996, 2829, 336807, 32304⟩,
    ⟨949, 9, 7, 4656, 4661, 7869, 3000, 382416, 31937⟩,
    ⟨949, 28, 5, 3521, 3526, 6644, 5292, 1301809, 26413⟩,
    ⟨949, 46, 4, 3024, 3029, 6107, 6783, 2227222, 23127⟩,
    ⟨949, 64, 4, 2694, 2699, 5750, 8000, 3182780, 20739⟩,
    ⟨949, 82, 4, 2446, 2451, 5483, 9056, 4156840, 18846⟩,
    ⟨949, 100, 3, 2248, 2253, 5269, 10000, 5148756, 17322⟩,
    ⟨949, 118, 3, 2082, 2087, 5089, 10863, 6164180, 16054⟩,
    ⟨949, 136, 3, 1940, 1945, 4936, 11662, 7183274, 14951⟩,
    ⟨949, 154, 3, 1816, 1821, 4802, 12410, 8213304, 13998⟩,
    ⟨949, 172, 2, 1705, 1710, 4682, 13115, 9260474, 13159⟩,
    ⟨949, 190, 2, 1606, 1611, 4575, 13785, 10306299, 12412⟩,
    ⟨949, 208, 2, 1515, 1520, 4477, 14423, 11367464, 11736⟩,
    ⟨949, 226, 2, 1432, 1437, 4387, 15034, 12437987, 11133⟩,
    ⟨949, 244, 2, 1356, 1361, 4305, 15621, 13500885, 10581⟩,
    ⟨949, 262, 2, 1285, 1290, 4229, 16187, 14566950, 10069⟩,
    ⟨949, 280, 2, 1218, 1223, 4156, 16734, 15670113, 9610⟩,
    ⟨949, 298, 2, 1156, 1161, 4089, 17263, 16755981, 9183⟩,
    ⟨949, 316, 2, 1097, 1102, 4026, 17777, 17845569, 8779⟩,
    ⟨949, 334, 2, 1042, 1047, 3966, 18276, 18949078, 8417⟩,
    ⟨949, 352, 1, 989, 994, 3909, 18762, 20060551, 8071⟩,
    ⟨949, 370, 1, 939, 944, 3855, 19236, 21173603, 7750⟩,
    ⟨949, 388, 1, 892, 897, 3804, 19698, 22281467, 7452⟩,
    ⟨949, 406, 1, 847, 852, 3756, 20150, 23377061, 7167⟩,
    ⟨949, 424, 1, 803, 808, 3708, 20592, 24526527, 6903⟩,
    ⟨949, 442, 1, 762, 767, 3664, 21024, 25629788, 6653⟩,
    ⟨949, 460, 1, 722, 727, 3621, 21448, 26755907, 6415⟩,
    ⟨949, 478, 1, 683, 688, 3579, 21864, 27903587, 6190⟩,
    ⟨949, 496, 1, 646, 651, 3539, 22272, 29042354, 5978⟩,
    ⟨949, 514, 1, 611, 616, 3501, 22672, 30167201, 5781⟩,
    ⟨949, 532, 1, 576, 581, 3463, 23066, 31335613, 5590⟩,
    ⟨949, 550, 1, 543, 548, 3427, 23453, 32484247, 5411⟩,
    ⟨949, 568, 1, 511, 516, 3393, 23833, 33607702, 5236⟩,
    ⟨949, 586, 1, 480, 485, 3359, 24208, 34770011, 5075⟩,
    ⟨949, 604, 1, 449, 454, 3326, 24577, 35936564, 4914⟩,
    ⟨949, 622, 1, 420, 425, 3294, 24940, 37105131, 4768⟩,
    ⟨949, 640, 1, 391, 396, 3263, 25299, 38273405, 4622⟩,
    ⟨949, 658, 1, 364, 369, 3234, 25652, 39399584, 4486⟩,
    ⟨949, 676, 0, 337, 342, 3205, 26000, 40558901, 4354⟩,
    ⟨949, 694, 0, 310, 315, 3176, 26344, 41752330, 4226⟩,
    ⟨949, 712, 0, 285, 290, 3149, 26684, 42895000, 4107⟩,
    ⟨949, 730, 0, 260, 265, 3122, 27019, 44068942, 3991⟩,
    ⟨949, 748, 0, 236, 241, 3096, 27350, 45229760, 3881⟩,
    ⟨949, 766, 0, 212, 217, 3070, 27677, 46421154, 3774⟩,
    ⟨949, 784, 0, 188, 193, 3044, 28000, 47643932, 3669⟩,
    ⟨949, 802, 0, 166, 171, 3020, 28320, 48801218, 3573⟩,
    ⟨949, 820, 0, 144, 149, 2996, 28636, 49986615, 3479⟩,
    ⟨949, 838, 0, 122, 127, 2973, 28949, 51149630, 3384⟩,
    ⟨949, 856, 0, 101, 106, 2950, 29258, 52339705, 3297⟩,
    ⟨949, 874, 0, 80, 85, 2927, 29564, 53557469, 3212⟩,
    ⟨949, 892, 0, 59, 64, 2905, 29867, 54748790, 3126⟩,
    ⟨949, 910, 0, 39, 44, 2883, 30167, 55966610, 3047⟩,
    ⟨949, 928, 0, 20, 25, 2862, 30464, 57154337, 2973⟩,
    ⟨949, 946, 0, 1, 6, 2842, 30758, 58308931, 2898⟩,
    ⟨949, 949, 0, -2, 2, 2838, 30806, 58542634, 2889⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell20_rows_check : ∀ r ∈ target028Cell20Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell20Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 949)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell20RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell20Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨949, 949, 0, -2, 2, 2838, 30806, 58542634, 2889⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell20Weight (n : ℕ) : ℚ :=
  ((target028Cell20RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell20_select :
    ∀ n ∈ target028Cell20Prefix,
      1 ≤ n ∧
        target028Cell20RowFor n ∈ target028Cell20Rows ∧
        n ≤ (target028Cell20RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell20RowFor n).b) ∧ (target028Cell20RowFor n).cut = 949 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell20_sum_check :
    (78457 / 10000 : ℚ) <
      ∑ n ∈ target028Cell20Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell20Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell20_principal :
    (78457 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(949 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 949 n).re := by
  have hs : target028Cell20Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell20Prefix ⊆ Finset.Ioc 0 ⌊(949 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell20_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell20Prefix, 0 ≤ target028Cell20Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell20Prefix, (target028Cell20Weight n : ℝ) ≤ refinedScaledWeight 949 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell20_select n hn
    have hcheck := target028_cell20_rows_check (target028Cell20RowFor n) hm
    have hrow := (target028Cell20RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell20RowFor n).b ≤ 949 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 949 (target028Cell20RowFor n).b ≤ refinedScaledWeight 949 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 949) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell20Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 949) target028Cell20Prefix
      target028Cell20Weight hs ht hw0 hw
  have hr :
    ((78457 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell20Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell20Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell20_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell20_budget :
    target028MomentBudget 949 (60225 / 1000) ≤ 4 * (78457 / 10000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 949 10 32 0 (68557 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 949 0 (38057 / 62500000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 949 ≤ (68557 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (949 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (38057 / 62500000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (7701 / 250 : ℝ) ≤ Real.sqrt 949 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 949 ≤ (30807 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 949) (U := 60225 / 1000) (L := 68557 / 10000) (P :=
      38057 / 62500000) (s := 7701 / 250) (t := 30807 / 1000) (by norm_num only) (by norm_num only)
      hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell20_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (58225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 60225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (949 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 949) (U := 60225 / 1000) (S := 78457 / 10000) (by norm_num only) hU hcut
      (le_of_lt target028_cell20_principal) target028_cell20_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
