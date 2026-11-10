/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 22 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 1084. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell22Rows : List Target028GeneralWeightRow :=
  [⟨1084, 2, 9, 6293, 6298, 9637, 1415, 65268, 31858⟩,
    ⟨1084, 3, 8, 5887, 5892, 9199, 1733, 101140, 31931⟩,
    ⟨1084, 4, 8, 5600, 5605, 8889, 2000, 137897, 31779⟩,
    ⟨1084, 5, 8, 5376, 5381, 8647, 2237, 175653, 31524⟩,
    ⟨1084, 7, 7, 5040, 5045, 8284, 2646, 252525, 30918⟩,
    ⟨1084, 8, 7, 4906, 4911, 8139, 2829, 291928, 30608⟩,
    ⟨1084, 9, 7, 4789, 4794, 8013, 3000, 331129, 30274⟩,
    ⟨1084, 31, 5, 3552, 3557, 6677, 5568, 1259550, 24908⟩,
    ⟨1084, 52, 4, 3035, 3040, 6119, 7212, 2200655, 21702⟩,
    ⟨1084, 73, 4, 2695, 2700, 5751, 8545, 3179599, 19415⟩,
    ⟨1084, 94, 4, 2443, 2448, 5479, 9696, 4173501, 17620⟩,
    ⟨1084, 115, 3, 2241, 2246, 5261, 10724, 5190112, 16166⟩,
    ⟨1084, 136, 3, 2073, 2078, 5080, 11662, 6219909, 14945⟩,
    ⟨1084, 157, 3, 1930, 1935, 4925, 12530, 7262726, 13916⟩,
    ⟨1084, 178, 3, 1804, 1809, 4789, 13342, 8320773, 13013⟩,
    ⟨1084, 199, 2, 1693, 1698, 4669, 14107, 9381646, 12223⟩,
    ⟨1084, 220, 2, 1592, 1597, 4560, 14833, 10462058, 11517⟩,
    ⟨1084, 241, 2, 1501, 1506, 4462, 15525, 11539261, 10882⟩,
    ⟨1084, 262, 2, 1418, 1423, 4372, 16187, 12625963, 10317⟩,
    ⟨1084, 283, 2, 1340, 1345, 4288, 16823, 13732362, 9794⟩,
    ⟨1084, 304, 2, 1269, 1274, 4211, 17436, 14831529, 9325⟩,
    ⟨1084, 325, 2, 1202, 1207, 4139, 18028, 15938782, 8886⟩,
    ⟨1084, 346, 2, 1139, 1144, 4071, 18602, 17060319, 8484⟩,
    ⟨1084, 367, 2, 1081, 1086, 4008, 19158, 18169698, 8118⟩,
    ⟨1084, 388, 1, 1025, 1030, 3948, 19698, 19293249, 7769⟩,
    ⟨1084, 409, 1, 972, 977, 3891, 20224, 20424910, 7446⟩,
    ⟨1084, 430, 1, 922, 927, 3837, 20737, 21558178, 7146⟩,
    ⟨1084, 451, 1, 874, 879, 3785, 21237, 22708862, 6866⟩,
    ⟨1084, 472, 1, 829, 834, 3736, 21726, 23849309, 6607⟩,
    ⟨1084, 493, 1, 785, 790, 3689, 22204, 24996986, 6355⟩,
    ⟨1084, 514, 1, 744, 749, 3644, 22672, 26147544, 6128⟩,
    ⟨1084, 535, 1, 704, 709, 3601, 23131, 27296412, 5907⟩,
    ⟨1084, 556, 1, 665, 670, 3559, 23580, 28467277, 5697⟩,
    ⟨1084, 577, 1, 628, 633, 3519, 24021, 29629049, 5501⟩,
    ⟨1084, 598, 1, 592, 597, 3480, 24455, 30807411, 5314⟩,
    ⟨1084, 619, 1, 558, 563, 3444, 24880, 31936682, 5135⟩,
    ⟨1084, 640, 1, 524, 529, 3407, 25299, 33140472, 4966⟩,
    ⟨1084, 661, 1, 492, 497, 3372, 25710, 34320926, 4809⟩,
    ⟨1084, 682, 1, 461, 466, 3339, 26116, 35472412, 4654⟩,
    ⟨1084, 703, 1, 431, 436, 3306, 26515, 36662530, 4512⟩,
    ⟨1084, 724, 1, 401, 406, 3274, 26908, 37854704, 4370⟩,
    ⟨1084, 745, 1, 373, 378, 3244, 27295, 39007552, 4238⟩,
    ⟨1084, 766, 1, 345, 350, 3213, 27677, 40235724, 4113⟩,
    ⟨1084, 787, 0, 318, 323, 3184, 28054, 41419644, 3991⟩,
    ⟨1084, 808, 0, 291, 296, 3155, 28426, 42638400, 3872⟩,
    ⟨1084, 829, 0, 266, 271, 3128, 28793, 43805320, 3761⟩,
    ⟨1084, 850, 0, 241, 246, 3101, 29155, 45004175, 3654⟩,
    ⟨1084, 871, 0, 216, 221, 3074, 29513, 46235841, 3550⟩,
    ⟨1084, 892, 0, 192, 197, 3048, 29867, 47453736, 3451⟩,
    ⟨1084, 913, 0, 169, 174, 3023, 30216, 48655034, 3357⟩,
    ⟨1084, 934, 0, 146, 151, 2999, 30562, 49836880, 3262⟩,
    ⟨1084, 955, 0, 124, 129, 2975, 30904, 51047433, 3175⟩,
    ⟨1084, 976, 0, 102, 107, 2951, 31241, 52287392, 3090⟩,
    ⟨1084, 997, 0, 81, 86, 2928, 31576, 53503939, 3010⟩,
    ⟨1084, 1018, 0, 60, 65, 2906, 31907, 54694069, 2928⟩,
    ⟨1084, 1039, 0, 40, 45, 2884, 32234, 55910672, 2854⟩,
    ⟨1084, 1060, 0, 20, 25, 2862, 32558, 57154337, 2782⟩,
    ⟨1084, 1081, 0, 0, 5, 2841, 32879, 58367269, 2709⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell22_rows_check : ∀ r ∈ target028Cell22Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell22Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 1084)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell22RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell22Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨1084, 1081, 0, 0, 5, 2841, 32879, 58367269, 2709⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell22Weight (n : ℕ) : ℚ :=
  ((target028Cell22RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell22_select :
    ∀ n ∈ target028Cell22Prefix,
      1 ≤ n ∧
        target028Cell22RowFor n ∈ target028Cell22Rows ∧
        n ≤ (target028Cell22RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell22RowFor n).b) ∧ (target028Cell22RowFor n).cut = 1084 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell22_sum_check :
    (5268 / 625 : ℚ) <
      ∑ n ∈ target028Cell22Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell22Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell22_principal :
    (5268 / 625 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(1084 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 1084 n).re := by
  have hs : target028Cell22Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell22Prefix ⊆ Finset.Ioc 0 ⌊(1084 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell22_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell22Prefix, 0 ≤ target028Cell22Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell22Prefix, (target028Cell22Weight n : ℝ) ≤ refinedScaledWeight 1084 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell22_select n hn
    have hcheck := target028_cell22_rows_check (target028Cell22RowFor n) hm
    have hrow := (target028Cell22RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell22RowFor n).b ≤ 1084 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 1084 (target028Cell22RowFor n).b ≤ refinedScaledWeight 1084 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 1084) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell22Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 1084) target028Cell22Prefix
      target028EulerData2701 target028Cell22Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((5268 / 625 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell22Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell22Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell22_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell22_budget :
    target028MomentBudget 1084 (64225 / 1000) ≤ 4 * (5268 / 625 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1084 10 32 0 (69887 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1084 0 (527437 / 1000000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 1084 ≤ (69887 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (1084 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (527437 / 1000000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (32923 / 1000 : ℝ) ≤ Real.sqrt 1084 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 1084 ≤ (16463 / 500 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 1084) (U := 64225 / 1000) (L := 69887 / 10000) (P :=
      527437 / 1000000000) (s := 32923 / 1000) (t := 16463 / 500) (by norm_num only)
      (by norm_num only) hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell22_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (62225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 64225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1084 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 1084) (U := 64225 / 1000) (S := 5268 / 625) (by norm_num only) hU hcut
      (le_of_lt target028_cell22_principal) target028_cell22_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
