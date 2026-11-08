/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 34 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 2081. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell34Rows : List Target028GeneralWeightRow :=
  [⟨2081, 2, 10, 6945, 6950, 10342, 1415, 32249, 22400⟩,
    ⟨2081, 3, 9, 6539, 6544, 9903, 1733, 50024, 22842⟩,
    ⟨2081, 4, 9, 6252, 6257, 9593, 2000, 68204, 23016⟩,
    ⟨2081, 5, 9, 6029, 6034, 9352, 2237, 86791, 23058⟩,
    ⟨2081, 7, 8, 5692, 5697, 8988, 2646, 124899, 23000⟩,
    ⟨2081, 8, 8, 5559, 5564, 8845, 2829, 144100, 22897⟩,
    ⟨2081, 9, 8, 5441, 5446, 8717, 3000, 163777, 22822⟩,
    ⟨2081, 51, 5, 3706, 3711, 6843, 7142, 1066897, 18603⟩,
    ⟨2081, 92, 4, 3116, 3121, 6206, 9592, 2017290, 16059⟩,
    ⟨2081, 133, 4, 2748, 2753, 5809, 11533, 3000429, 14264⟩,
    ⟨2081, 174, 4, 2479, 2484, 5518, 13191, 4013867, 12905⟩,
    ⟨2081, 215, 3, 2267, 2272, 5289, 14663, 5046804, 11807⟩,
    ⟨2081, 256, 3, 2093, 2098, 5101, 16000, 6090652, 10896⟩,
    ⟨2081, 297, 3, 1944, 1949, 4940, 17234, 7154598, 10121⟩,
    ⟨2081, 338, 3, 1815, 1820, 4801, 18385, 8221521, 9448⟩,
    ⟨2081, 379, 2, 1701, 1706, 4678, 19468, 9297590, 8859⟩,
    ⟨2081, 420, 2, 1598, 1603, 4567, 20494, 10389080, 8336⟩,
    ⟨2081, 461, 2, 1505, 1510, 4466, 21471, 11493196, 7875⟩,
    ⟨2081, 502, 2, 1420, 1425, 4374, 22406, 12600736, 7456⟩,
    ⟨2081, 543, 2, 1341, 1346, 4289, 23303, 13718637, 7072⟩,
    ⟨2081, 584, 2, 1268, 1273, 4210, 24167, 14846368, 6726⟩,
    ⟨2081, 625, 2, 1200, 1205, 4137, 25000, 15970691, 6404⟩,
    ⟨2081, 666, 2, 1137, 1142, 4069, 25807, 17094474, 6111⟩,
    ⟨2081, 707, 2, 1077, 1082, 4004, 26590, 18242522, 5840⟩,
    ⟨2081, 748, 1, 1021, 1026, 3944, 27350, 19370577, 5587⟩,
    ⟨2081, 789, 1, 967, 972, 3885, 28090, 20547828, 5355⟩,
    ⟨2081, 830, 1, 917, 922, 3831, 28810, 21687916, 5138⟩,
    ⟨2081, 871, 1, 868, 873, 3778, 29513, 22868382, 4933⟩,
    ⟨2081, 912, 1, 822, 827, 3729, 30200, 24016840, 4738⟩,
    ⟨2081, 953, 1, 778, 783, 3681, 30871, 25197764, 4560⟩,
    ⟨2081, 994, 1, 736, 741, 3636, 31528, 26357563, 4390⟩,
    ⟨2081, 1035, 1, 696, 701, 3593, 32172, 27515659, 4230⟩,
    ⟨2081, 1076, 1, 657, 662, 3550, 32803, 28724639, 4082⟩,
    ⟨2081, 1117, 1, 620, 625, 3510, 33422, 29896914, 3940⟩,
    ⟨2081, 1158, 1, 584, 589, 3472, 34030, 31054858, 3802⟩,
    ⟨2081, 1199, 1, 549, 554, 3434, 34627, 32257651, 3674⟩,
    ⟨2081, 1240, 1, 515, 520, 3397, 35214, 33473540, 3552⟩,
    ⟨2081, 1281, 1, 483, 488, 3363, 35792, 34631209, 3435⟩,
    ⟨2081, 1322, 1, 451, 456, 3328, 36360, 35864762, 3325⟩,
    ⟨2081, 1363, 1, 421, 426, 3296, 36919, 37030995, 3220⟩,
    ⟨2081, 1404, 1, 391, 396, 3263, 37470, 38273405, 3121⟩,
    ⟨2081, 1445, 1, 362, 367, 3232, 38014, 39478462, 3023⟩,
    ⟨2081, 1486, 0, 334, 339, 3202, 38549, 40680760, 2931⟩,
    ⟨2081, 1527, 0, 307, 312, 3172, 39077, 41919674, 2846⟩,
    ⟨2081, 1568, 0, 281, 286, 3144, 39598, 43110012, 2762⟩,
    ⟨2081, 1609, 0, 255, 260, 3116, 40113, 44334150, 2681⟩,
    ⟨2081, 1650, 0, 230, 235, 3089, 40621, 45547479, 2604⟩,
    ⟨2081, 1691, 0, 205, 210, 3062, 41122, 46794013, 2529⟩,
    ⟨2081, 1732, 0, 181, 186, 3036, 41618, 48026612, 2457⟩,
    ⟨2081, 1773, 0, 158, 163, 3012, 42108, 49193193, 2388⟩,
    ⟨2081, 1814, 0, 135, 140, 2987, 42592, 50438525, 2322⟩,
    ⟨2081, 1855, 0, 112, 117, 2962, 43070, 51715382, 2258⟩,
    ⟨2081, 1896, 0, 91, 96, 2939, 43544, 52918620, 2199⟩,
    ⟨2081, 1937, 0, 69, 74, 2915, 44012, 54204030, 2139⟩,
    ⟨2081, 1978, 0, 48, 53, 2893, 44475, 55409733, 2081⟩,
    ⟨2081, 2019, 0, 28, 33, 2871, 44934, 56642255, 2028⟩,
    ⟨2081, 2060, 0, 8, 13, 2850, 45388, 57844320, 1974⟩,
    ⟨2081, 2081, 0, -2, 2, 2838, 45618, 58542634, 1951⟩]

-- Exact reduction checks the finite endpoint certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell34_rows_check : ∀ r ∈ target028Cell34Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell34Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 2081)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell34RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell34Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨2081, 2081, 0, -2, 2, 2838, 45618, 58542634, 1951⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell34Weight (n : ℕ) : ℚ :=
  ((target028Cell34RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell34_select :
    ∀ n ∈ target028Cell34Prefix,
      1 ≤ n ∧
        target028Cell34RowFor n ∈ target028Cell34Rows ∧
        n ≤ (target028Cell34RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell34RowFor n).b) ∧ (target028Cell34RowFor n).cut = 2081 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell34_sum_check :
    (583 / 50 : ℚ) <
      ∑ n ∈ target028Cell34Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell34Weight n := by
  decide +kernel

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 1000000 in
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell34_principal :
    (583 / 50 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(2081 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 2081 n).re := by
  have hs : target028Cell34Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell34Prefix ⊆ Finset.Ioc 0 ⌊(2081 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell34_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell34Prefix, 0 ≤ target028Cell34Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell34Prefix, (target028Cell34Weight n : ℝ) ≤ refinedScaledWeight 2081 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell34_select n hn
    have hcheck := target028_cell34_rows_check (target028Cell34RowFor n) hm
    have hrow := (target028Cell34RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell34RowFor n).b ≤ 2081 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 2081 (target028Cell34RowFor n).b ≤ refinedScaledWeight 2081 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 2081) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell34Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 2081) target028Cell34Prefix
      target028EulerData2701 target028Cell34Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((583 / 50 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell34Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell34Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell34_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell34_budget :
    target028MomentBudget 2081 (88225 / 1000) ≤ 4 * (583 / 50 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 2081 11 32 0 (76409 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 2081 0 (130389 / 500000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 2081 ≤ (76409 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (2081 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (130389 / 500000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (5702 / 125 : ℝ) ≤ Real.sqrt 2081 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 2081 ≤ (45619 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 2081) (U := 88225 / 1000) (L := 76409 / 10000) (P :=
      130389 / 500000000) (s := 5702 / 125) (t := 45619 / 1000) (by norm_num only)
      (by norm_num only) hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell34_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (86225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 88225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (2081 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 2081) (U := 88225 / 1000) (S := 583 / 50) (by norm_num only) hU hcut
      (le_of_lt target028_cell34_principal) target028_cell34_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
