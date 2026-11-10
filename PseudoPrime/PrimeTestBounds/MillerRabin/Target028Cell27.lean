/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 27 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 1460. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell27Rows : List Target028GeneralWeightRow :=
  [⟨1460, 2, 10, 6591, 6596, 9959, 1415, 47300, 27211⟩,
    ⟨1460, 3, 9, 6185, 6190, 9521, 1733, 73296, 27485⟩,
    ⟨1460, 4, 9, 5897, 5902, 9210, 2000, 100034, 27527⟩,
    ⟨1460, 5, 8, 5674, 5679, 8969, 2237, 127295, 27429⟩,
    ⟨1460, 7, 8, 5338, 5343, 8606, 2646, 183004, 27113⟩,
    ⟨1460, 8, 8, 5204, 5209, 8461, 2829, 211560, 26932⟩,
    ⟨1460, 9, 7, 5086, 5091, 8334, 3000, 240209, 26727⟩,
    ⟨1460, 39, 5, 3620, 3625, 6750, 6245, 1170879, 21806⟩,
    ⟨1460, 68, 4, 3064, 3069, 6150, 8247, 2133481, 18876⟩,
    ⟨1460, 97, 4, 2709, 2714, 5767, 9849, 3129130, 16797⟩,
    ⟨1460, 126, 4, 2447, 2452, 5484, 11225, 4152685, 15204⟩,
    ⟨1460, 155, 3, 2240, 2245, 5260, 12450, 5195304, 13924⟩,
    ⟨1460, 184, 3, 2069, 2074, 5075, 13565, 6251086, 12858⟩,
    ⟨1460, 213, 3, 1922, 1927, 4917, 14595, 7321061, 11938⟩,
    ⟨1460, 242, 3, 1795, 1800, 4779, 15557, 8404399, 11159⟩,
    ⟨1460, 271, 2, 1682, 1687, 4657, 16463, 9494904, 10466⟩,
    ⟨1460, 300, 2, 1580, 1585, 4547, 17321, 10598953, 9850⟩,
    ⟨1460, 329, 2, 1488, 1493, 4448, 18139, 11701947, 9297⟩,
    ⟨1460, 358, 2, 1403, 1408, 4356, 18921, 12829603, 8803⟩,
    ⟨1460, 387, 2, 1325, 1330, 4272, 19673, 13953847, 8351⟩,
    ⟨1460, 416, 2, 1253, 1258, 4194, 20397, 15085820, 7942⟩,
    ⟨1460, 445, 2, 1186, 1191, 4122, 21096, 16212057, 7564⟩,
    ⟨1460, 474, 2, 1122, 1127, 4053, 21772, 17370185, 7215⟩,
    ⟨1460, 503, 2, 1063, 1068, 3989, 22428, 18518223, 6897⟩,
    ⟨1460, 532, 1, 1007, 1012, 3928, 23066, 19682999, 6603⟩,
    ⟨1460, 561, 1, 954, 959, 3871, 23686, 20837521, 6325⟩,
    ⟨1460, 590, 1, 904, 909, 3817, 24290, 21993683, 6068⟩,
    ⟨1460, 619, 1, 856, 861, 3765, 24880, 23167612, 5827⟩,
    ⟨1460, 648, 1, 810, 815, 3716, 25456, 24331097, 5596⟩,
    ⟨1460, 677, 1, 766, 771, 3668, 26020, 25527473, 5386⟩,
    ⟨1460, 706, 1, 724, 729, 3623, 26571, 26702448, 5183⟩,
    ⟨1460, 735, 1, 684, 689, 3580, 27111, 27875698, 4994⟩,
    ⟨1460, 764, 1, 645, 650, 3537, 27641, 29100497, 4819⟩,
    ⟨1460, 793, 1, 608, 613, 3498, 28161, 30257838, 4646⟩,
    ⟨1460, 822, 1, 572, 577, 3459, 28671, 31461207, 4487⟩,
    ⟨1460, 851, 1, 537, 542, 3421, 29172, 32679738, 4335⟩,
    ⟨1460, 880, 1, 504, 509, 3385, 29665, 33877642, 4194⟩,
    ⟨1460, 909, 1, 471, 476, 3350, 30150, 35084354, 4052⟩,
    ⟨1460, 938, 1, 440, 445, 3316, 30627, 36297732, 3925⟩,
    ⟨1460, 967, 1, 409, 414, 3283, 31097, 37515541, 3797⟩,
    ⟨1460, 996, 1, 380, 385, 3251, 31560, 38735452, 3682⟩,
    ⟨1460, 1025, 1, 351, 356, 3220, 32016, 39955058, 3567⟩,
    ⟨1460, 1054, 0, 323, 328, 3190, 32466, 41171870, 3457⟩,
    ⟨1460, 1083, 0, 296, 301, 3161, 32909, 42383336, 3353⟩,
    ⟨1460, 1112, 0, 270, 275, 3132, 33347, 43630448, 3257⟩,
    ⟨1460, 1141, 0, 244, 249, 3104, 33779, 44869365, 3161⟩,
    ⟨1460, 1170, 0, 219, 224, 3077, 34206, 46097341, 3070⟩,
    ⟨1460, 1199, 0, 194, 199, 3050, 34627, 47358924, 2981⟩,
    ⟨1460, 1228, 0, 171, 176, 3026, 35043, 48509287, 2896⟩,
    ⟨1460, 1257, 0, 147, 152, 3000, 35455, 49787068, 2814⟩,
    ⟨1460, 1286, 0, 124, 129, 2975, 35861, 51047433, 2736⟩,
    ⟨1460, 1315, 0, 102, 107, 2951, 36263, 52287392, 2662⟩,
    ⟨1460, 1344, 0, 80, 85, 2927, 36661, 53557469, 2590⟩,
    ⟨1460, 1373, 0, 59, 64, 2905, 37055, 54748790, 2519⟩,
    ⟨1460, 1402, 0, 38, 43, 2882, 37444, 56022605, 2453⟩,
    ⟨1460, 1431, 0, 18, 23, 2860, 37829, 57268760, 2390⟩,
    ⟨1460, 1460, 0, -2, 2, 2838, 38210, 58542634, 2329⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell27_rows_check : ∀ r ∈ target028Cell27Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell27Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 1460)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell27RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell27Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨1460, 1460, 0, -2, 2, 2838, 38210, 58542634, 2329⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell27Weight (n : ℕ) : ℚ :=
  ((target028Cell27RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell27_select :
    ∀ n ∈ target028Cell27Prefix,
      1 ≤ n ∧
        target028Cell27RowFor n ∈ target028Cell27Rows ∧
        n ≤ (target028Cell27RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell27RowFor n).b) ∧ (target028Cell27RowFor n).cut = 1460 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell27_sum_check :
    (48807 / 5000 : ℚ) <
      ∑ n ∈ target028Cell27Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell27Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell27_principal :
    (48807 / 5000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(1460 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 1460 n).re := by
  have hs : target028Cell27Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell27Prefix ⊆ Finset.Ioc 0 ⌊(1460 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell27_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell27Prefix, 0 ≤ target028Cell27Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell27Prefix, (target028Cell27Weight n : ℝ) ≤ refinedScaledWeight 1460 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell27_select n hn
    have hcheck := target028_cell27_rows_check (target028Cell27RowFor n) hm
    have hrow := (target028Cell27RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell27RowFor n).b ≤ 1460 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 1460 (target028Cell27RowFor n).b ≤ refinedScaledWeight 1460 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 1460) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell27Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 1460) target028Cell27Prefix
      target028EulerData2701 target028Cell27Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((48807 / 5000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell27Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell27Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell27_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell27_budget :
    target028MomentBudget 1460 (74225 / 1000) ≤ 4 * (48807 / 5000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1460 11 32 0 (4554 / 625) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1460 0 (191193 / 500000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 1460 ≤ (4554 / 625 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (1460 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (191193 / 500000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (4776 / 125 : ℝ) ≤ Real.sqrt 1460 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 1460 ≤ (38211 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 1460) (U := 74225 / 1000) (L := 4554 / 625) (P :=
      191193 / 500000000) (s := 4776 / 125) (t := 38211 / 1000) (by norm_num only)
      (by norm_num only) hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell27_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (72225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 74225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1460 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 1460) (U := 74225 / 1000) (S := 48807 / 5000) (by norm_num only) hU hcut
      (le_of_lt target028_cell27_principal) target028_cell27_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
