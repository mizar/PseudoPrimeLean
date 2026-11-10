/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 36 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 2279. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell36Rows : List Target028GeneralWeightRow :=
  [⟨2279, 2, 10, 7036, 7041, 10440, 1415, 29239, 21293⟩,
    ⟨2279, 3, 10, 6630, 6635, 10001, 1733, 45354, 21758⟩,
    ⟨2279, 4, 9, 6343, 6348, 9691, 2000, 61837, 21960⟩,
    ⟨2279, 5, 9, 6120, 6125, 9450, 2237, 78689, 22028⟩,
    ⟨2279, 7, 8, 5783, 5788, 9087, 2646, 113126, 21997⟩,
    ⟨2279, 8, 8, 5650, 5655, 8943, 2829, 130648, 21940⟩,
    ⟨2279, 9, 8, 5532, 5537, 8815, 3000, 148488, 21885⟩,
    ⟨2279, 55, 5, 3722, 3727, 6861, 7417, 1047865, 17817⟩,
    ⟨2279, 100, 5, 3124, 3129, 6215, 10000, 1999216, 15373⟩,
    ⟨2279, 145, 4, 2752, 2757, 5813, 12042, 2988451, 13657⟩,
    ⟨2279, 190, 4, 2482, 2487, 5521, 13785, 4001844, 12348⟩,
    ⟨2279, 235, 3, 2269, 2274, 5291, 15330, 5036721, 11294⟩,
    ⟨2279, 280, 3, 2094, 2099, 5102, 16734, 6084565, 10418⟩,
    ⟨2279, 325, 3, 1945, 1950, 4941, 18028, 7147447, 9676⟩,
    ⟨2279, 370, 3, 1815, 1820, 4801, 19236, 8221521, 9030⟩,
    ⟨2279, 415, 2, 1701, 1706, 4678, 20372, 9297590, 8466⟩,
    ⟨2279, 460, 2, 1598, 1603, 4567, 21448, 10389080, 7965⟩,
    ⟨2279, 505, 2, 1504, 1509, 4465, 22473, 11504695, 7522⟩,
    ⟨2279, 550, 2, 1419, 1424, 4373, 23453, 12613343, 7122⟩,
    ⟨2279, 595, 2, 1340, 1345, 4288, 24393, 13732362, 6755⟩,
    ⟨2279, 640, 2, 1268, 1273, 4210, 25299, 14846368, 6425⟩,
    ⟨2279, 685, 2, 1200, 1205, 4137, 26173, 15970691, 6117⟩,
    ⟨2279, 730, 2, 1136, 1141, 4068, 27019, 17111577, 5835⟩,
    ⟨2279, 775, 2, 1076, 1081, 4003, 27839, 18260774, 5576⟩,
    ⟨2279, 820, 1, 1020, 1025, 3942, 28636, 19409357, 5339⟩,
    ⟨2279, 865, 1, 966, 971, 3884, 29411, 20568386, 5113⟩,
    ⟨2279, 910, 1, 916, 921, 3830, 30167, 21709615, 4905⟩,
    ⟨2279, 955, 1, 867, 872, 3777, 30904, 22891262, 4709⟩,
    ⟨2279, 1000, 1, 821, 826, 3728, 31623, 24040869, 4523⟩,
    ⟨2279, 1045, 1, 777, 782, 3680, 32327, 25222974, 4353⟩,
    ⟨2279, 1090, 1, 735, 740, 3635, 33016, 26383934, 4190⟩,
    ⟨2279, 1135, 1, 695, 700, 3591, 33690, 27570745, 4041⟩,
    ⟨2279, 1180, 1, 656, 661, 3549, 34352, 28753378, 3896⟩,
    ⟨2279, 1225, 1, 618, 623, 3508, 35000, 29956768, 3759⟩,
    ⟨2279, 1270, 1, 582, 587, 3469, 35638, 31148163, 3630⟩,
    ⟨2279, 1315, 1, 547, 552, 3432, 36263, 32322231, 3504⟩,
    ⟨2279, 1360, 1, 514, 519, 3396, 36879, 33507030, 3390⟩,
    ⟨2279, 1405, 1, 481, 486, 3360, 37484, 34735258, 3279⟩,
    ⟨2279, 1450, 1, 450, 455, 3327, 38079, 35900645, 3173⟩,
    ⟨2279, 1495, 1, 419, 424, 3293, 38666, 37142255, 3073⟩,
    ⟨2279, 1540, 1, 389, 394, 3261, 39243, 38350028, 2976⟩,
    ⟨2279, 1585, 1, 361, 366, 3231, 39813, 39517961, 2885⟩,
    ⟨2279, 1630, 0, 333, 338, 3201, 40374, 40721462, 2796⟩,
    ⟨2279, 1675, 0, 305, 310, 3170, 40927, 42003597, 2713⟩,
    ⟨2279, 1720, 0, 279, 284, 3142, 41473, 43196318, 2633⟩,
    ⟨2279, 1765, 0, 253, 258, 3114, 42012, 44422907, 2556⟩,
    ⟨2279, 1810, 0, 228, 233, 3087, 42545, 45638665, 2482⟩,
    ⟨2279, 1855, 0, 203, 208, 3060, 43070, 46887695, 2411⟩,
    ⟨2279, 1900, 0, 179, 184, 3034, 43589, 48122761, 2343⟩,
    ⟨2279, 1945, 0, 156, 161, 3009, 44103, 49340995, 2278⟩,
    ⟨2279, 1990, 0, 133, 138, 2985, 44610, 50539503, 2213⟩,
    ⟨2279, 2035, 0, 111, 116, 2961, 45111, 51767124, 2154⟩,
    ⟨2279, 2080, 0, 89, 94, 2937, 45608, 53024563, 2096⟩,
    ⟨2279, 2125, 0, 67, 72, 2913, 46098, 54312547, 2039⟩,
    ⟨2279, 2170, 0, 47, 52, 2892, 46584, 55465171, 1985⟩,
    ⟨2279, 2215, 0, 26, 31, 2869, 47064, 56755653, 1933⟩,
    ⟨2279, 2260, 0, 6, 11, 2847, 47540, 58018114, 1883⟩,
    ⟨2279, 2279, 0, -2, 2, 2838, 47739, 58542634, 1864⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell36_rows_check : ∀ r ∈ target028Cell36Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell36Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 2279)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell36RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell36Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨2279, 2279, 0, -2, 2, 2838, 47739, 58542634, 1864⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell36Weight (n : ℕ) : ℚ :=
  ((target028Cell36RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell36_select :
    ∀ n ∈ target028Cell36Prefix,
      1 ≤ n ∧
        target028Cell36RowFor n ∈ target028Cell36Rows ∧
        n ≤ (target028Cell36RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell36RowFor n).b) ∧ (target028Cell36RowFor n).cut = 2279 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell36_sum_check :
    (121821 / 10000 : ℚ) <
      ∑ n ∈ target028Cell36Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell36Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell36_principal :
    (121821 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(2279 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 2279 n).re := by
  have hs : target028Cell36Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell36Prefix ⊆ Finset.Ioc 0 ⌊(2279 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell36_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell36Prefix, 0 ≤ target028Cell36Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell36Prefix, (target028Cell36Weight n : ℝ) ≤ refinedScaledWeight 2279 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell36_select n hn
    have hcheck := target028_cell36_rows_check (target028Cell36RowFor n) hm
    have hrow := (target028Cell36RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell36RowFor n).b ≤ 2279 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 2279 (target028Cell36RowFor n).b ≤ refinedScaledWeight 2279 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 2279) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell36Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 2279) target028Cell36Prefix
      target028EulerData2701 target028Cell36Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((121821 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell36Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell36Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell36_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell36_budget :
    target028MomentBudget 2279 (92225 / 1000) ≤ 4 * (121821 / 10000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 2279 11 32 0 (77317 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 2279 0 (59099 / 250000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 2279 ≤ (77317 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (2279 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (59099 / 250000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (47737 / 1000 : ℝ) ≤ Real.sqrt 2279 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 2279 ≤ (2387 / 50 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 2279) (U := 92225 / 1000) (L := 77317 / 10000) (P :=
      59099 / 250000000) (s := 47737 / 1000) (t := 2387 / 50) (by norm_num only) (by norm_num only)
      hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell36_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (90225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 92225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (2279 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 2279) (U := 92225 / 1000) (S := 121821 / 10000) (by norm_num only) hU
      hcut (le_of_lt target028_cell36_principal) target028_cell36_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
