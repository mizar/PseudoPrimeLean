/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral

/-! # Uniform analytic cell 2 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 259. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell02Rows : List Target028GeneralWeightRow :=
  [⟨259, 2, 7, 4861, 4866, 8091, 1415, 306283, 62309⟩,
    ⟨259, 3, 6, 4456, 4461, 7653, 1733, 474618, 59697⟩,
    ⟨259, 4, 6, 4168, 4173, 7342, 2000, 647753, 57362⟩,
    ⟨259, 5, 6, 3945, 3950, 7101, 2237, 824280, 55229⟩,
    ⟨259, 7, 5, 3608, 3613, 6738, 2646, 1185014, 51588⟩,
    ⟨259, 8, 5, 3475, 3480, 6594, 2829, 1368554, 50028⟩,
    ⟨259, 9, 5, 3357, 3362, 6466, 3000, 1555435, 48629⟩,
    ⟨259, 15, 4, 2846, 2851, 5915, 3873, 2698659, 41818⟩,
    ⟨259, 20, 4, 2559, 2564, 5605, 4473, 3679420, 37708⟩,
    ⟨259, 25, 3, 2335, 2340, 5363, 5000, 4686824, 34455⟩,
    ⟨259, 30, 3, 2153, 2158, 5166, 5478, 5707352, 31767⟩,
    ⟨259, 35, 3, 1999, 2004, 5000, 5917, 6737946, 29474⟩,
    ⟨259, 40, 3, 1865, 1870, 4855, 6325, 7789333, 27517⟩,
    ⟨259, 45, 3, 1748, 1753, 4729, 6709, 8835301, 25786⟩,
    ⟨259, 50, 2, 1642, 1647, 4614, 7072, 9912090, 24275⟩,
    ⟨259, 55, 2, 1547, 1552, 4512, 7417, 10976485, 22903⟩,
    ⟨259, 60, 2, 1460, 1465, 4418, 7746, 12058324, 21682⟩,
    ⟨259, 65, 2, 1380, 1385, 4331, 8063, 13154386, 20583⟩,
    ⟨259, 70, 2, 1306, 1311, 4251, 8367, 14249976, 19574⟩,
    ⟨259, 75, 2, 1237, 1242, 4177, 8661, 15344471, 18637⟩,
    ⟨259, 80, 2, 1172, 1177, 4107, 8945, 16457071, 17779⟩,
    ⟨259, 85, 2, 1112, 1117, 4042, 9220, 17562312, 16998⟩,
    ⟨259, 90, 2, 1055, 1060, 3980, 9487, 18685639, 16276⟩,
    ⟨259, 100, 1, 949, 954, 3866, 10000, 20941969, 14952⟩,
    ⟨259, 105, 1, 900, 905, 3813, 10247, 22081833, 14360⟩,
    ⟨259, 110, 1, 854, 859, 3763, 10489, 23213993, 13811⟩,
    ⟨259, 115, 1, 809, 814, 3715, 10724, 24355441, 13279⟩,
    ⟨259, 125, 1, 726, 731, 3625, 11181, 26649097, 12331⟩,
    ⟨259, 130, 1, 687, 692, 3583, 11402, 27792196, 11894⟩,
    ⟨259, 135, 1, 649, 654, 3542, 11619, 28955358, 11478⟩,
    ⟨259, 140, 1, 613, 618, 3503, 11833, 30106927, 11089⟩,
    ⟨259, 150, 1, 544, 549, 3428, 12248, 32451779, 10368⟩,
    ⟨259, 155, 1, 511, 516, 3393, 12450, 33607702, 10025⟩,
    ⟨259, 160, 1, 479, 484, 3358, 12650, 34804798, 9707⟩,
    ⟨259, 165, 1, 448, 453, 3325, 12846, 35972518, 9396⟩,
    ⟨259, 170, 1, 419, 424, 3293, 13039, 37142255, 9115⟩,
    ⟨259, 175, 1, 390, 395, 3262, 13229, 38311697, 8834⟩,
    ⟨259, 180, 1, 361, 366, 3231, 13417, 39517961, 8561⟩,
    ⟨259, 185, 0, 334, 339, 3202, 13602, 40680760, 8307⟩,
    ⟨259, 195, 0, 281, 286, 3144, 13965, 43110012, 7833⟩,
    ⟨259, 200, 0, 256, 261, 3117, 14143, 44289838, 7610⟩,
    ⟨259, 215, 0, 184, 189, 3040, 14663, 47834889, 6985⟩,
    ⟨259, 225, 0, 138, 143, 2990, 15000, 50287436, 6610⟩,
    ⟨259, 230, 0, 116, 121, 2966, 15166, 51508934, 6434⟩,
    ⟨259, 235, 0, 95, 100, 2943, 15330, 52707369, 6267⟩,
    ⟨259, 240, 0, 74, 79, 2921, 15492, 53879780, 6099⟩,
    ⟨259, 245, 0, 53, 58, 2898, 15653, 55133376, 5940⟩,
    ⟨259, 255, 0, 13, 18, 2855, 15969, 57555821, 5637⟩,
    ⟨259, 259, 0, -2, 2, 2838, 16094, 58542634, 5530⟩]

-- Exact reduction checks the finite endpoint certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell02_rows_check : ∀ r ∈ target028Cell02Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell02Prefix : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 259)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell02RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell02Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨259, 259, 0, -2, 2, 2838, 16094, 58542634, 5530⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell02Weight (n : ℕ) : ℚ :=
  ((target028Cell02RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell02_select :
    ∀ n ∈ target028Cell02Prefix,
      1 ≤ n ∧
        target028Cell02RowFor n ∈ target028Cell02Rows ∧
        n ≤ (target028Cell02RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell02RowFor n).b) ∧ (target028Cell02RowFor n).cut = 259 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell02_sum_check :
    (40559 / 10000 : ℚ) <
      ∑ n ∈ target028Cell02Prefix,
        refinedPsiLower n (refinedEulerData n) * target028Cell02Weight n := by
  decide +kernel

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 1000000 in
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell02_principal :
    (40559 / 10000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(259 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 259 n).re := by
  have hs : target028Cell02Prefix ⊆ refinedEulerPrefixSet := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell02Prefix ⊆ Finset.Ioc 0 ⌊(259 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell02_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell02Prefix, 0 ≤ target028Cell02Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell02Prefix, (target028Cell02Weight n : ℝ) ≤ refinedScaledWeight 259 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell02_select n hn
    have hcheck := target028_cell02_rows_check (target028Cell02RowFor n) hm
    have hrow := (target028Cell02RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell02RowFor n).b ≤ 259 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 259 (target028Cell02RowFor n).b ≤ refinedScaledWeight 259 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 259) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell02Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_rows_lower (by norm_num only : (0 : ℝ) < 259) target028Cell02Prefix
      target028Cell02Weight hs ht hw0 hw
  have hr :
    ((40559 / 10000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell02Prefix,
            refinedPsiLower n (refinedEulerData n) * target028Cell02Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell02_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell02_budget :
    target028MomentBudget 259 (30960 / 1000) ≤ 4 * (40559 / 10000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 259 8 32 0 (55571 / 10000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 259 0 (49507 / 20000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 259 ≤ (55571 / 10000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (259 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (49507 / 20000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (4023 / 250 : ℝ) ≤ Real.sqrt 259 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 259 ≤ (3219 / 200 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 259) (U := 30960 / 1000) (L := 55571 / 10000) (P :=
      49507 / 20000000) (s := 4023 / 250) (t := 3219 / 200) (by norm_num only) (by norm_num only) hl
      hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell02_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (30461 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 30960 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (259 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 259) (U := 30960 / 1000) (S := 40559 / 10000) (by norm_num only) hU hcut
      (le_of_lt target028_cell02_principal) target028_cell02_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
