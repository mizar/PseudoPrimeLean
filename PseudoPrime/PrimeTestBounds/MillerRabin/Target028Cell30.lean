/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 30 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 1713. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell30Rows : List Target028GeneralWeightRow :=
  [⟨1713, 2, 10, 6750, 6755, 10131, 1415, 39825, 24957⟩,
    ⟨1713, 3, 9, 6345, 6350, 9693, 1733, 61713, 25320⟩,
    ⟨1713, 4, 9, 6057, 6062, 9382, 2000, 84226, 25436⟩,
    ⟨1713, 5, 8, 5834, 5839, 9142, 2237, 107072, 25382⟩,
    ⟨1713, 7, 8, 5498, 5503, 8779, 2646, 153931, 25191⟩,
    ⟨1713, 8, 8, 5364, 5369, 8634, 2829, 177951, 25064⟩,
    ⟨1713, 9, 8, 5246, 5251, 8507, 3000, 202049, 24912⟩,
    ⟨1713, 44, 5, 3659, 3664, 6793, 6634, 1121598, 20285⟩,
    ⟨1713, 78, 4, 3087, 3092, 6175, 8832, 2080805, 17540⟩,
    ⟨1713, 112, 4, 2725, 2730, 5784, 10584, 3076385, 15599⟩,
    ⟨1713, 146, 4, 2460, 2465, 5498, 12084, 4094953, 14106⟩,
    ⟨1713, 180, 3, 2251, 2256, 5272, 13417, 5133333, 12912⟩,
    ⟨1713, 214, 3, 2078, 2083, 5085, 14629, 6188887, 11918⟩,
    ⟨1713, 248, 3, 1930, 1935, 4925, 15749, 7262726, 11072⟩,
    ⟨1713, 282, 3, 1802, 1807, 4787, 16793, 8337432, 10336⟩,
    ⟨1713, 316, 2, 1688, 1693, 4664, 17777, 9428672, 9692⟩,
    ⟨1713, 350, 2, 1586, 1591, 4554, 18709, 10525019, 9120⟩,
    ⟨1713, 384, 2, 1493, 1498, 4453, 19596, 11643583, 8615⟩,
    ⟨1713, 418, 2, 1408, 1413, 4362, 20446, 12752856, 8148⟩,
    ⟨1713, 452, 2, 1330, 1335, 4277, 21261, 13884252, 7737⟩,
    ⟨1713, 486, 2, 1257, 1262, 4198, 22046, 15025597, 7357⟩,
    ⟨1713, 520, 2, 1190, 1195, 4126, 22804, 16147339, 7006⟩,
    ⟨1713, 554, 2, 1126, 1131, 4057, 23538, 17300843, 6682⟩,
    ⟨1713, 588, 2, 1067, 1072, 3993, 24249, 18444298, 6388⟩,
    ⟨1713, 622, 1, 1011, 1016, 3933, 24940, 19584829, 6110⟩,
    ⟨1713, 656, 1, 957, 962, 3874, 25613, 20775102, 5856⟩,
    ⟨1713, 690, 1, 907, 912, 3820, 26268, 21927800, 5618⟩,
    ⟨1713, 724, 1, 859, 864, 3769, 26908, 23075126, 5390⟩,
    ⟨1713, 758, 1, 813, 818, 3719, 27532, 24258213, 5181⟩,
    ⟨1713, 792, 1, 769, 774, 3671, 28143, 25451006, 4986⟩,
    ⟨1713, 826, 1, 727, 732, 3626, 28741, 26622461, 4799⟩,
    ⟨1713, 860, 1, 687, 692, 3583, 29326, 27792196, 4624⟩,
    ⟨1713, 894, 1, 648, 653, 3541, 29900, 28984328, 4458⟩,
    ⟨1713, 928, 1, 610, 615, 3500, 30464, 30197383, 4300⟩,
    ⟨1713, 962, 1, 574, 579, 3461, 31017, 31398347, 4152⟩,
    ⟨1713, 996, 1, 540, 545, 3424, 31560, 32581846, 4014⟩,
    ⟨1713, 1030, 1, 506, 511, 3387, 32094, 33809954, 3881⟩,
    ⟨1713, 1064, 1, 474, 479, 3353, 32620, 34979258, 3752⟩,
    ⟨1713, 1098, 1, 442, 447, 3318, 33137, 36225209, 3632⟩,
    ⟨1713, 1132, 1, 412, 417, 3286, 33646, 37403163, 3516⟩,
    ⟨1713, 1166, 1, 382, 387, 3253, 34147, 38658059, 3407⟩,
    ⟨1713, 1200, 1, 353, 358, 3222, 34642, 39875227, 3301⟩,
    ⟨1713, 1234, 0, 325, 330, 3192, 35129, 41089609, 3199⟩,
    ⟨1713, 1268, 0, 298, 303, 3163, 35609, 42298654, 3103⟩,
    ⟨1713, 1302, 0, 272, 277, 3135, 36084, 43499753, 3011⟩,
    ⟨1713, 1336, 0, 246, 251, 3107, 36552, 44734959, 2923⟩,
    ⟨1713, 1370, 0, 221, 226, 3080, 37014, 45959256, 2838⟩,
    ⟨1713, 1404, 0, 196, 201, 3053, 37470, 47217060, 2756⟩,
    ⟨1713, 1438, 0, 172, 177, 3027, 37921, 48460802, 2678⟩,
    ⟨1713, 1472, 0, 149, 154, 3002, 38367, 49687593, 2604⟩,
    ⟨1713, 1506, 0, 126, 131, 2977, 38808, 50945441, 2532⟩,
    ⟨1713, 1540, 0, 104, 109, 2953, 39243, 52182922, 2464⟩,
    ⟨1713, 1574, 0, 82, 87, 2929, 39674, 53450461, 2397⟩,
    ⟨1713, 1608, 0, 61, 66, 2907, 40100, 54639402, 2332⟩,
    ⟨1713, 1642, 0, 40, 45, 2884, 40522, 55910672, 2271⟩,
    ⟨1713, 1676, 0, 19, 24, 2861, 40939, 57211520, 2211⟩,
    ⟨1713, 1710, 0, -1, 4, 2840, 41353, 58425665, 2152⟩]

-- Exact reduction checks the finite endpoint certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell30_rows_check : ∀ r ∈ target028Cell30Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell30Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 1713)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell30RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell30Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨1713, 1710, 0, -1, 4, 2840, 41353, 58425665, 2152⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell30Weight (n : ℕ) : ℚ :=
  ((target028Cell30RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell30_select :
    ∀ n ∈ target028Cell30Prefix,
      1 ≤ n ∧
        target028Cell30RowFor n ∈ target028Cell30Rows ∧
        n ≤ (target028Cell30RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell30RowFor n).b) ∧ (target028Cell30RowFor n).cut = 1713 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell30_sum_check :
    (21209 / 2000 : ℚ) <
      ∑ n ∈ target028Cell30Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell30Weight n := by
  decide +kernel

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 1000000 in
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell30_principal :
    (21209 / 2000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(1713 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 1713 n).re := by
  have hs : target028Cell30Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell30Prefix ⊆ Finset.Ioc 0 ⌊(1713 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell30_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell30Prefix, 0 ≤ target028Cell30Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell30Prefix, (target028Cell30Weight n : ℝ) ≤ refinedScaledWeight 1713 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell30_select n hn
    have hcheck := target028_cell30_rows_check (target028Cell30RowFor n) hm
    have hrow := (target028Cell30RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell30RowFor n).b ≤ 1713 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 1713 (target028Cell30RowFor n).b ≤ refinedScaledWeight 1713 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 1713) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell30Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 1713) target028Cell30Prefix
      target028EulerData2701 target028Cell30Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((21209 / 2000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell30Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell30Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell30_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell30_budget :
    target028MomentBudget 1713 (80225 / 1000) ≤ 4 * (21209 / 2000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1713 11 32 0 (74463 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1713 0 (32177 / 100000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 1713 ≤ (74463 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (1713 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (32177 / 100000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (41387 / 1000 : ℝ) ≤ Real.sqrt 1713 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 1713 ≤ (4139 / 100 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 1713) (U := 80225 / 1000) (L := 74463 / 10000) (P :=
      32177 / 100000000) (s := 41387 / 1000) (t := 4139 / 100) (by norm_num only) (by norm_num only)
      hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell30_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (78225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 80225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (1713 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 1713) (U := 80225 / 1000) (S := 21209 / 2000) (by norm_num only) hU hcut
      (le_of_lt target028_cell30_principal) target028_cell30_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
