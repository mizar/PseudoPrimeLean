/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral

/-! # Uniform analytic cell 8 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 350. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell08Rows : List Target028GeneralWeightRow :=
  [⟨350, 2, 7, 5162, 5167, 8416, 1415, 221298, 54828⟩,
    ⟨350, 3, 7, 4757, 4762, 7978, 1733, 342924, 53113⟩,
    ⟨350, 4, 6, 4469, 4474, 7667, 2000, 468019, 51478⟩,
    ⟨350, 5, 6, 4246, 4251, 7427, 2237, 594969, 49873⟩,
    ⟨350, 7, 6, 3910, 3915, 7064, 2646, 855349, 47175⟩,
    ⟨350, 8, 5, 3776, 3781, 6919, 2829, 988818, 45989⟩,
    ⟨350, 9, 5, 3658, 3663, 6792, 3000, 1122721, 44866⟩,
    ⟨350, 17, 4, 3022, 3027, 6105, 4124, 2231681, 38048⟩,
    ⟨350, 24, 4, 2677, 2682, 5732, 4899, 3240589, 33935⟩,
    ⟨350, 31, 3, 2421, 2426, 5456, 5568, 4270604, 30723⟩,
    ⟨350, 38, 3, 2218, 2223, 5236, 6165, 5321500, 28158⟩,
    ⟨350, 45, 3, 2049, 2054, 5054, 6709, 6383747, 25989⟩,
    ⟨350, 52, 3, 1904, 1909, 4897, 7212, 7468956, 24163⟩,
    ⟨350, 59, 3, 1778, 1783, 4761, 7682, 8557048, 22569⟩,
    ⟨350, 66, 2, 1666, 1671, 4640, 8125, 9657697, 21172⟩,
    ⟨350, 73, 2, 1565, 1570, 4531, 8545, 10769900, 19929⟩,
    ⟨350, 80, 2, 1473, 1478, 4432, 8945, 11890684, 18811⟩,
    ⟨350, 87, 2, 1390, 1395, 4342, 9328, 13010481, 17818⟩,
    ⟨350, 94, 2, 1312, 1317, 4258, 9696, 14150575, 16902⟩,
    ⟨350, 101, 2, 1240, 1245, 4180, 10050, 15298507, 16075⟩,
    ⟨350, 108, 2, 1173, 1178, 4108, 10393, 16440622, 15306⟩,
    ⟨350, 115, 2, 1111, 1116, 4041, 10724, 17579883, 14609⟩,
    ⟨350, 122, 2, 1051, 1056, 3976, 11046, 18760531, 13959⟩,
    ⟨350, 129, 1, 996, 1001, 3917, 11358, 19900707, 13355⟩,
    ⟨350, 136, 1, 943, 948, 3859, 11662, 21089078, 12804⟩,
    ⟨350, 143, 1, 893, 898, 3805, 11959, 22259197, 12280⟩,
    ⟨350, 150, 1, 845, 850, 3753, 12248, 23447298, 11792⟩,
    ⟨350, 157, 1, 799, 804, 3704, 12530, 24624829, 11324⟩,
    ⟨350, 164, 1, 756, 761, 3657, 12807, 25809826, 10901⟩,
    ⟨350, 171, 1, 714, 719, 3612, 13077, 26997797, 10491⟩,
    ⟨350, 178, 1, 674, 679, 3569, 13342, 28184023, 10107⟩,
    ⟨350, 185, 1, 635, 640, 3527, 13602, 29392962, 9742⟩,
    ⟨350, 192, 1, 598, 603, 3487, 13857, 30592512, 9401⟩,
    ⟨350, 199, 1, 562, 567, 3448, 14107, 31809191, 9077⟩,
    ⟨350, 213, 1, 494, 499, 3374, 14595, 34252353, 8482⟩,
    ⟨350, 227, 1, 430, 435, 3305, 15067, 36699211, 7936⟩,
    ⟨350, 234, 1, 400, 405, 3273, 15298, 37892578, 7682⟩,
    ⟨350, 241, 1, 371, 376, 3242, 15525, 39085645, 7441⟩,
    ⟨350, 248, 0, 342, 347, 3210, 15749, 40356613, 7214⟩,
    ⟨350, 255, 0, 314, 319, 3180, 15969, 41585655, 6991⟩,
    ⟨350, 262, 0, 287, 292, 3151, 16187, 42809296, 6780⟩,
    ⟨350, 269, 0, 261, 266, 3123, 16402, 44024895, 6579⟩,
    ⟨350, 276, 0, 235, 240, 3095, 16614, 45275012, 6384⟩,
    ⟨350, 283, 0, 210, 215, 3068, 16823, 46514090, 6199⟩,
    ⟨350, 290, 0, 186, 191, 3042, 17030, 47739315, 6024⟩,
    ⟨350, 297, 0, 162, 167, 3016, 17234, 48996814, 5853⟩,
    ⟨350, 311, 0, 116, 121, 2966, 17636, 51508934, 5533⟩,
    ⟨350, 318, 0, 93, 98, 2941, 17833, 52812889, 5378⟩,
    ⟨350, 332, 0, 50, 55, 2895, 18221, 55299025, 5089⟩,
    ⟨350, 339, 0, 29, 34, 2872, 18412, 56585641, 4955⟩,
    ⟨350, 346, 0, 9, 14, 2851, 18602, 57786505, 4822⟩,
    ⟨350, 350, 0, -2, 2, 2838, 18709, 58542634, 4757⟩]

-- Exact reduction checks the finite endpoint certificates.
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell08_rows_check : ∀ r ∈ target028Cell08Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell08Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 350)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell08RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell08Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨350, 350, 0, -2, 2, 2838, 18709, 58542634, 4757⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell08Weight (n : ℕ) : ℚ :=
  ((target028Cell08RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell08_select :
    ∀ n ∈ target028Cell08Prefix,
      1 ≤ n ∧
        target028Cell08RowFor n ∈ target028Cell08Rows ∧
        n ≤ (target028Cell08RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell08RowFor n).b) ∧ (target028Cell08RowFor n).cut = 350 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell08_sum_check :
    (2969 / 625 : ℚ) <
      ∑ n ∈ target028Cell08Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell08Weight n := by
  decide +kernel

set_option maxRecDepth 2000 in
-- Applying the certified prime-power prefix exceeds the default recursion depth.
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell08_principal :
    (2969 / 625 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(350 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 350 n).re := by
  have hs : target028Cell08Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell08Prefix ⊆ Finset.Ioc 0 ⌊(350 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell08_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell08Prefix, 0 ≤ target028Cell08Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell08Prefix, (target028Cell08Weight n : ℝ) ≤ refinedScaledWeight 350 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell08_select n hn
    have hcheck := target028_cell08_rows_check (target028Cell08RowFor n) hm
    have hrow := (target028Cell08RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell08RowFor n).b ≤ 350 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 350 (target028Cell08RowFor n).b ≤ refinedScaledWeight 350 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 350) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell08Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 350) target028Cell08Prefix
      target028Cell08Weight hs ht hw0 hw
  have hr :
    ((2969 / 625 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell08Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell08Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell08_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell08_budget :
    target028MomentBudget 350 (36776 / 1000) ≤ 4 * (2969 / 625 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 350 8 32 0 (29291 / 5000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 350 0 (1788163 / 1000000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 350 ≤ (29291 / 5000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (350 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (1788163 / 1000000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (18707 / 1000 : ℝ) ≤ Real.sqrt 350 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 350 ≤ (1871 / 100 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 350) (U := 36776 / 1000) (L := 29291 / 5000) (P :=
      1788163 / 1000000000) (s := 18707 / 1000) (t := 1871 / 100) (by norm_num only)
      (by norm_num only) hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell08_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (35392 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 36776 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (350 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 350) (U := 36776 / 1000) (S := 2969 / 625) (by norm_num only) hU hcut
      (le_of_lt target028_cell08_principal) target028_cell08_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
