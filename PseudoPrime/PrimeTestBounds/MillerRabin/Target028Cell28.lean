/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 28 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 1542. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell28Rows : List Target028GeneralWeightRow :=
  [⟨1542, 2, 10, 6645, 6650, 10018, 1415, 44590, 26412⟩,
    ⟨1542, 3, 9, 6240, 6245, 9580, 1733, 69096, 26729⟩,
    ⟨1542, 4, 9, 5952, 5957, 9269, 2000, 94302, 26798⟩,
    ⟨1542, 5, 8, 5729, 5734, 9028, 2237, 120002, 26725⟩,
    ⟨1542, 7, 8, 5392, 5397, 8664, 2646, 172692, 26465⟩,
    ⟨1542, 8, 8, 5259, 5264, 8521, 2829, 199240, 26267⟩,
    ⟨1542, 9, 7, 5141, 5146, 8393, 3000, 226446, 26107⟩,
    ⟨1542, 40, 5, 3649, 3654, 6782, 6325, 1134004, 21340⟩,
    ⟨1542, 70, 4, 3090, 3095, 6178, 8367, 2074572, 18508⟩,
    ⟨1542, 100, 4, 2733, 2738, 5793, 10000, 3048821, 16484⟩,
    ⟨1542, 130, 4, 2471, 2476, 5510, 11402, 4046107, 14932⟩,
    ⟨1542, 160, 3, 2263, 2268, 5285, 12650, 5067032, 13685⟩,
    ⟨1542, 190, 3, 2091, 2096, 5099, 13785, 6102846, 12645⟩,
    ⟨1542, 220, 3, 1945, 1950, 4941, 14833, 7147447, 11760⟩,
    ⟨1542, 250, 3, 1817, 1822, 4803, 15812, 8205094, 10988⟩,
    ⟨1542, 280, 2, 1704, 1709, 4681, 16734, 9269739, 10312⟩,
    ⟨1542, 310, 2, 1602, 1607, 4571, 17607, 10347606, 9710⟩,
    ⟨1542, 340, 2, 1509, 1514, 4471, 18440, 11435874, 9168⟩,
    ⟨1542, 370, 2, 1425, 1430, 4380, 19236, 12525358, 8687⟩,
    ⟨1542, 400, 2, 1347, 1352, 4296, 20000, 13622941, 8245⟩,
    ⟨1542, 430, 2, 1275, 1280, 4218, 20737, 14728071, 7846⟩,
    ⟨1542, 460, 2, 1207, 1212, 4144, 21448, 15859287, 7481⟩,
    ⟨1542, 490, 2, 1144, 1149, 4076, 22136, 16975230, 7141⟩,
    ⟨1542, 520, 2, 1085, 1090, 4013, 22804, 18079076, 6822⟩,
    ⟨1542, 550, 1, 1028, 1033, 3951, 23453, 19235456, 6532⟩,
    ⟨1542, 580, 1, 975, 980, 3894, 24084, 20363727, 6260⟩,
    ⟨1542, 610, 1, 925, 930, 3840, 24699, 21493601, 6007⟩,
    ⟨1542, 640, 1, 877, 882, 3788, 25299, 22640838, 5771⟩,
    ⟨1542, 670, 1, 831, 836, 3738, 25885, 23801658, 5550⟩,
    ⟨1542, 700, 1, 787, 792, 3691, 26458, 24947042, 5338⟩,
    ⟨1542, 730, 1, 745, 750, 3645, 27019, 26121409, 5145⟩,
    ⟨1542, 760, 1, 705, 710, 3602, 27569, 27269129, 4959⟩,
    ⟨1542, 790, 1, 666, 671, 3560, 28107, 28438824, 4782⟩,
    ⟨1542, 820, 1, 629, 634, 3520, 28636, 29599435, 4617⟩,
    ⟨1542, 850, 1, 593, 598, 3481, 29155, 30776618, 4460⟩,
    ⟨1542, 880, 1, 558, 563, 3444, 29665, 31936682, 4306⟩,
    ⟨1542, 910, 1, 525, 530, 3408, 30167, 33107348, 4167⟩,
    ⟨1542, 940, 1, 492, 497, 3372, 30660, 34320926, 4032⟩,
    ⟨1542, 970, 1, 461, 466, 3339, 31145, 35472412, 3903⟩,
    ⟨1542, 1000, 1, 431, 436, 3306, 31623, 36662530, 3783⟩,
    ⟨1542, 1030, 1, 401, 406, 3274, 32094, 37854704, 3664⟩,
    ⟨1542, 1060, 1, 372, 377, 3243, 32558, 39046579, 3550⟩,
    ⟨1542, 1090, 1, 344, 349, 3212, 33016, 40275980, 3445⟩,
    ⟨1542, 1120, 0, 317, 322, 3183, 33467, 41461085, 3343⟩,
    ⟨1542, 1150, 0, 291, 296, 3155, 33912, 42638400, 3245⟩,
    ⟨1542, 1180, 0, 265, 270, 3127, 34352, 43849147, 3150⟩,
    ⟨1542, 1210, 0, 240, 245, 3100, 34786, 45049202, 3060⟩,
    ⟨1542, 1240, 0, 215, 220, 3073, 35214, 46282100, 2973⟩,
    ⟨1542, 1270, 0, 192, 197, 3048, 35638, 47453736, 2892⟩,
    ⟨1542, 1300, 0, 168, 173, 3022, 36056, 48703713, 2811⟩,
    ⟨1542, 1330, 0, 145, 150, 2997, 36470, 49936653, 2734⟩,
    ⟨1542, 1360, 0, 123, 128, 2974, 36879, 51098506, 2658⟩,
    ⟨1542, 1390, 0, 101, 106, 2950, 37283, 52339705, 2587⟩,
    ⟨1542, 1420, 0, 80, 85, 2927, 37683, 53557469, 2520⟩,
    ⟨1542, 1450, 0, 59, 64, 2905, 38079, 54748790, 2452⟩,
    ⟨1542, 1480, 0, 39, 44, 2883, 38471, 55966610, 2390⟩,
    ⟨1542, 1510, 0, 18, 23, 2860, 38859, 57268760, 2327⟩,
    ⟨1542, 1540, 0, -1, 4, 2840, 39243, 58425665, 2267⟩]

-- Exact reduction checks the finite endpoint certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell28_rows_check : ∀ r ∈ target028Cell28Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell28Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 1542)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell28RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell28Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨1542, 1540, 0, -1, 4, 2840, 39243, 58425665, 2267⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell28Weight (n : ℕ) : ℚ :=
  ((target028Cell28RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell28_select :
    ∀ n ∈ target028Cell28Prefix,
      1 ≤ n ∧
        target028Cell28RowFor n ∈ target028Cell28Rows ∧
        n ≤ (target028Cell28RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell28RowFor n).b) ∧ (target028Cell28RowFor n).cut = 1542 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell28_sum_check :
    (99753 / 10000 : ℚ) <
      ∑ n ∈ target028Cell28Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell28Weight n := by
  decide +kernel

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 1000000 in
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell28_principal :
    (99753 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(1542 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 1542 n).re := by
  have hs : target028Cell28Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell28Prefix ⊆ Finset.Ioc 0 ⌊(1542 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell28_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell28Prefix, 0 ≤ target028Cell28Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell28Prefix, (target028Cell28Weight n : ℝ) ≤ refinedScaledWeight 1542 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell28_select n hn
    have hcheck := target028_cell28_rows_check (target028Cell28RowFor n) hm
    have hrow := (target028Cell28RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell28RowFor n).b ≤ 1542 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 1542 (target028Cell28RowFor n).b ≤ refinedScaledWeight 1542 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 1542) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell28Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 1542) target028Cell28Prefix
      target028EulerData2701 target028Cell28Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((99753 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell28Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell28Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell28_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell28_budget :
    target028MomentBudget 1542 (76225 / 1000) ≤ 4 * (99753 / 10000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1542 11 32 0 (73411 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1542 0 (45059 / 125000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 1542 ≤ (73411 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (1542 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (45059 / 125000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (39267 / 1000 : ℝ) ≤ Real.sqrt 1542 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 1542 ≤ (3927 / 100 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 1542) (U := 76225 / 1000) (L := 73411 / 10000) (P :=
      45059 / 125000000) (s := 39267 / 1000) (t := 3927 / 100) (by norm_num only) (by norm_num only)
      hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell28_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (74225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 76225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1542 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 1542) (U := 76225 / 1000) (S := 99753 / 10000) (by norm_num only) hU
      hcut (le_of_lt target028_cell28_principal) target028_cell28_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
