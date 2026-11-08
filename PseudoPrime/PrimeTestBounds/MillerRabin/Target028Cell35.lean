/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 35 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 2179. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell35Rows : List Target028GeneralWeightRow :=
  [⟨2179, 2, 10, 6991, 6996, 10391, 1415, 30707, 21846⟩,
    ⟨2179, 3, 10, 6586, 6591, 9954, 1733, 47537, 22269⟩,
    ⟨2179, 4, 9, 6298, 6303, 9643, 2000, 64878, 22467⟩,
    ⟨2179, 5, 9, 6075, 6080, 9402, 2237, 82558, 22523⟩,
    ⟨2179, 7, 8, 5738, 5743, 9038, 2646, 118808, 22490⟩,
    ⟨2179, 8, 8, 5605, 5610, 8894, 2829, 137209, 22422⟩,
    ⟨2179, 9, 8, 5487, 5492, 8767, 3000, 155790, 22335⟩,
    ⟨2179, 53, 5, 3714, 3719, 6852, 7281, 1057338, 18199⟩,
    ⟨2179, 96, 5, 3120, 3125, 6210, 9798, 2009237, 15713⟩,
    ⟨2179, 139, 4, 2750, 2755, 5811, 11790, 2994434, 13951⟩,
    ⟨2179, 182, 4, 2480, 2485, 5519, 13491, 4009855, 12618⟩,
    ⟨2179, 225, 3, 2268, 2273, 5290, 15000, 5041760, 11542⟩,
    ⟨2179, 268, 3, 2093, 2098, 5101, 16371, 6090652, 10649⟩,
    ⟨2179, 311, 3, 1944, 1949, 4940, 17636, 7154598, 9890⟩,
    ⟨2179, 354, 3, 1815, 1820, 4801, 18815, 8221521, 9232⟩,
    ⟨2179, 397, 2, 1700, 1705, 4677, 19925, 9306892, 8655⟩,
    ⟨2179, 440, 2, 1597, 1602, 4566, 20977, 10399474, 8143⟩,
    ⟨2179, 483, 2, 1504, 1509, 4465, 21978, 11504695, 7692⟩,
    ⟨2179, 526, 2, 1419, 1424, 4373, 22935, 12613343, 7283⟩,
    ⟨2179, 569, 2, 1340, 1345, 4288, 23854, 13732362, 6907⟩,
    ⟨2179, 612, 2, 1267, 1272, 4209, 24739, 14861222, 6568⟩,
    ⟨2179, 655, 2, 1199, 1204, 4136, 25593, 15986670, 6254⟩,
    ⟨2179, 698, 2, 1136, 1141, 4068, 26420, 17111577, 5967⟩,
    ⟨2179, 741, 2, 1076, 1081, 4003, 27222, 18260774, 5703⟩,
    ⟨2179, 784, 1, 1020, 1025, 3942, 28000, 19409357, 5461⟩,
    ⟨2179, 827, 1, 966, 971, 3884, 28758, 20568386, 5229⟩,
    ⟨2179, 870, 1, 916, 921, 3830, 29496, 21709615, 5017⟩,
    ⟨2179, 913, 1, 867, 872, 3777, 30216, 22891262, 4816⟩,
    ⟨2179, 956, 1, 821, 826, 3728, 30920, 24040869, 4626⟩,
    ⟨2179, 999, 1, 777, 782, 3680, 31607, 25222974, 4452⟩,
    ⟨2179, 1042, 1, 735, 740, 3635, 32281, 26383934, 4285⟩,
    ⟨2179, 1085, 1, 695, 700, 3591, 32940, 27570745, 4133⟩,
    ⟨2179, 1128, 1, 656, 661, 3549, 33586, 28753378, 3985⟩,
    ⟨2179, 1171, 1, 619, 624, 3509, 34220, 29926826, 3847⟩,
    ⟨2179, 1214, 1, 582, 587, 3469, 34843, 31148163, 3713⟩,
    ⟨2179, 1257, 1, 548, 553, 3433, 35455, 32289925, 3586⟩,
    ⟨2179, 1300, 1, 514, 519, 3396, 36056, 33507030, 3467⟩,
    ⟨2179, 1343, 1, 481, 486, 3360, 36647, 34735258, 3354⟩,
    ⟨2179, 1386, 1, 450, 455, 3327, 37230, 35900645, 3246⟩,
    ⟨2179, 1429, 1, 419, 424, 3293, 37803, 37142255, 3144⟩,
    ⟨2179, 1472, 1, 390, 395, 3262, 38367, 38311697, 3046⟩,
    ⟨2179, 1515, 1, 361, 366, 3231, 38924, 39517961, 2950⟩,
    ⟨2179, 1558, 0, 333, 338, 3201, 39472, 40721462, 2860⟩,
    ⟨2179, 1601, 0, 306, 311, 3171, 40013, 41961615, 2777⟩,
    ⟨2179, 1644, 0, 279, 284, 3142, 40547, 43196318, 2694⟩,
    ⟨2179, 1687, 0, 253, 258, 3114, 41074, 44422907, 2614⟩,
    ⟨2179, 1730, 0, 228, 233, 3087, 41594, 45638665, 2539⟩,
    ⟨2179, 1773, 0, 204, 209, 3061, 42108, 46840830, 2468⟩,
    ⟨2179, 1816, 0, 180, 185, 3035, 42615, 48074662, 2398⟩,
    ⟨2179, 1859, 0, 156, 161, 3009, 43117, 49340995, 2330⟩,
    ⟨2179, 1902, 0, 133, 138, 2985, 43612, 50539503, 2264⟩,
    ⟨2179, 1945, 0, 111, 116, 2961, 44103, 51767124, 2203⟩,
    ⟨2179, 1988, 0, 89, 94, 2937, 44587, 53024563, 2144⟩,
    ⟨2179, 2031, 0, 68, 73, 2914, 45067, 54258262, 2087⟩,
    ⟨2179, 2074, 0, 47, 52, 2892, 45542, 55465171, 2031⟩,
    ⟨2179, 2117, 0, 26, 31, 2869, 46011, 56755653, 1977⟩,
    ⟨2179, 2160, 0, 6, 11, 2847, 46476, 58018114, 1926⟩,
    ⟨2179, 2179, 0, -2, 2, 2838, 46680, 58542634, 1906⟩]

-- Exact reduction checks the finite endpoint certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell35_rows_check : ∀ r ∈ target028Cell35Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell35Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 2179)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell35RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell35Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨2179, 2179, 0, -2, 2, 2838, 46680, 58542634, 1906⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell35Weight (n : ℕ) : ℚ :=
  ((target028Cell35RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell35_select :
    ∀ n ∈ target028Cell35Prefix,
      1 ≤ n ∧
        target028Cell35RowFor n ∈ target028Cell35Rows ∧
        n ≤ (target028Cell35RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell35RowFor n).b) ∧ (target028Cell35RowFor n).cut = 2179 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell35_sum_check :
    (59747 / 5000 : ℚ) <
      ∑ n ∈ target028Cell35Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell35Weight n := by
  decide +kernel

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 1000000 in
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell35_principal :
    (59747 / 5000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(2179 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 2179 n).re := by
  have hs : target028Cell35Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell35Prefix ⊆ Finset.Ioc 0 ⌊(2179 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell35_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell35Prefix, 0 ≤ target028Cell35Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell35Prefix, (target028Cell35Weight n : ℝ) ≤ refinedScaledWeight 2179 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell35_select n hn
    have hcheck := target028_cell35_rows_check (target028Cell35RowFor n) hm
    have hrow := (target028Cell35RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell35RowFor n).b ≤ 2179 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 2179 (target028Cell35RowFor n).b ≤ refinedScaledWeight 2179 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 2179) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell35Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 2179) target028Cell35Prefix
      target028EulerData2701 target028Cell35Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((59747 / 5000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell35Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell35Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell35_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell35_budget :
    target028MomentBudget 2179 (90225 / 1000) ≤ 4 * (59747 / 5000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 2179 11 32 0 (76869 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 2179 0 (124067 / 500000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 2179 ≤ (76869 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (2179 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (124067 / 500000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (23339 / 500 : ℝ) ≤ Real.sqrt 2179 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 2179 ≤ (46681 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 2179) (U := 90225 / 1000) (L := 76869 / 10000) (P :=
      124067 / 500000000) (s := 23339 / 500) (t := 46681 / 1000) (by norm_num only)
      (by norm_num only) hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell35_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (88225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 90225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (2179 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 2179) (U := 90225 / 1000) (S := 59747 / 5000) (by norm_num only) hU hcut
      (le_of_lt target028_cell35_principal) target028_cell35_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
