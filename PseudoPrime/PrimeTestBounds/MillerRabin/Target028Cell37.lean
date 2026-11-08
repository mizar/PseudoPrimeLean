/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix2701

/-! # Uniform analytic cell 37 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational interval endpoints for cutoff 2381. All proposed logarithm,
exponential, root, and weight values are checked in the kernel below. -/
def target028Cell37Rows : List Target028GeneralWeightRow :=
  [⟨2381, 2, 10, 7080, 7085, 10487, 1415, 27896, 20782⟩,
    ⟨2381, 3, 10, 6674, 6679, 10049, 1733, 43228, 21236⟩,
    ⟨2381, 4, 9, 6386, 6391, 9738, 2000, 58998, 21459⟩,
    ⟨2381, 5, 9, 6163, 6168, 9497, 2237, 75076, 21538⟩,
    ⟨2381, 7, 8, 5827, 5832, 9134, 2646, 107932, 21542⟩,
    ⟨2381, 8, 8, 5693, 5698, 8989, 2829, 124774, 21504⟩,
    ⟨2381, 9, 8, 5576, 5581, 8863, 3000, 141529, 21428⟩,
    ⟨2381, 57, 5, 3730, 3735, 6869, 7550, 1039516, 17474⟩,
    ⟨2381, 104, 5, 3128, 3133, 6219, 10199, 1991235, 15065⟩,
    ⟨2381, 151, 4, 2755, 2760, 5816, 12289, 2979499, 13380⟩,
    ⟨2381, 198, 4, 2485, 2490, 5525, 14072, 3985868, 12083⟩,
    ⟨2381, 245, 3, 2272, 2277, 5295, 15653, 5016614, 11050⟩,
    ⟨2381, 292, 3, 2096, 2101, 5105, 17089, 6066338, 10193⟩,
    ⟨2381, 339, 3, 1947, 1952, 4944, 18412, 7126037, 9467⟩,
    ⟨2381, 386, 3, 1817, 1822, 4803, 19647, 8205094, 8843⟩,
    ⟨2381, 433, 2, 1702, 1707, 4679, 20809, 9288297, 8290⟩,
    ⟨2381, 480, 2, 1599, 1604, 4568, 21909, 10378696, 7799⟩,
    ⟨2381, 527, 2, 1506, 1511, 4467, 22957, 11481709, 7367⟩,
    ⟨2381, 574, 2, 1420, 1425, 4374, 23959, 12600736, 6973⟩,
    ⟨2381, 621, 2, 1341, 1346, 4289, 24920, 13718637, 6613⟩,
    ⟨2381, 668, 2, 1268, 1273, 4210, 25846, 14846368, 6289⟩,
    ⟨2381, 715, 2, 1200, 1205, 4137, 26740, 15970691, 5987⟩,
    ⟨2381, 762, 2, 1137, 1142, 4069, 27605, 17094474, 5713⟩,
    ⟨2381, 809, 2, 1077, 1082, 4004, 28443, 18242522, 5460⟩,
    ⟨2381, 856, 1, 1021, 1026, 3944, 29258, 19370577, 5222⟩,
    ⟨2381, 903, 1, 967, 972, 3885, 30050, 20547828, 5006⟩,
    ⟨2381, 950, 1, 916, 921, 3830, 30823, 21709615, 4801⟩,
    ⟨2381, 997, 1, 868, 873, 3778, 31576, 22868382, 4611⟩,
    ⟨2381, 1044, 1, 822, 827, 3729, 32311, 24016840, 4429⟩,
    ⟨2381, 1091, 1, 778, 783, 3681, 33031, 25197764, 4262⟩,
    ⟨2381, 1138, 1, 736, 741, 3636, 33735, 26357563, 4103⟩,
    ⟨2381, 1185, 1, 695, 700, 3591, 34424, 27570745, 3955⟩,
    ⟨2381, 1232, 1, 656, 661, 3549, 35100, 28753378, 3813⟩,
    ⟨2381, 1279, 1, 619, 624, 3509, 35764, 29926826, 3680⟩,
    ⟨2381, 1326, 1, 583, 588, 3471, 36415, 31085929, 3551⟩,
    ⟨2381, 1373, 1, 548, 553, 3433, 37055, 32289925, 3431⟩,
    ⟨2381, 1420, 1, 514, 519, 3396, 37683, 33507030, 3318⟩,
    ⟨2381, 1467, 1, 482, 487, 3361, 38302, 34700541, 3211⟩,
    ⟨2381, 1514, 1, 450, 455, 3327, 38911, 35900645, 3105⟩,
    ⟨2381, 1561, 1, 420, 425, 3294, 39510, 37105131, 3010⟩,
    ⟨2381, 1608, 1, 390, 395, 3262, 40100, 38311697, 2914⟩,
    ⟨2381, 1655, 1, 361, 366, 3231, 40682, 39517961, 2823⟩,
    ⟨2381, 1702, 0, 333, 338, 3201, 41256, 40721462, 2736⟩,
    ⟨2381, 1749, 0, 306, 311, 3171, 41822, 41961615, 2657⟩,
    ⟨2381, 1796, 0, 279, 284, 3142, 42380, 43196318, 2577⟩,
    ⟨2381, 1843, 0, 254, 259, 3115, 42931, 44378507, 2503⟩,
    ⟨2381, 1890, 0, 228, 233, 3087, 43475, 45638665, 2429⟩,
    ⟨2381, 1937, 0, 204, 209, 3061, 44012, 46840830, 2361⟩,
    ⟨2381, 1984, 0, 180, 185, 3035, 44543, 48074662, 2294⟩,
    ⟨2381, 2031, 0, 156, 161, 3009, 45067, 49340995, 2229⟩,
    ⟨2381, 2078, 0, 134, 139, 2986, 45586, 50488989, 2168⟩,
    ⟨2381, 2125, 0, 111, 116, 2961, 46098, 51767124, 2108⟩,
    ⟨2381, 2172, 0, 89, 94, 2937, 46605, 53024563, 2051⟩,
    ⟨2381, 2219, 0, 68, 73, 2914, 47107, 54258262, 1997⟩,
    ⟨2381, 2266, 0, 47, 52, 2892, 47603, 55465171, 1943⟩,
    ⟨2381, 2313, 0, 26, 31, 2869, 48094, 56755653, 1891⟩,
    ⟨2381, 2360, 0, 6, 11, 2847, 48580, 58018114, 1843⟩,
    ⟨2381, 2381, 0, -2, 2, 2838, 48796, 58542634, 1823⟩]

-- Exact reduction checks the finite endpoint certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each row contains a logarithmic and an exponential fixed-point check.
/-- Every weight endpoint for this cell passes its rational certificate. -/
theorem target028_cell37_rows_check : ∀ r ∈ target028Cell37Rows, r.check = true := by decide +kernel

/-- The checked prime-power prefix retained below the cutoff. -/
def target028Cell37Prefix : Finset ℕ :=
  target028EulerSet2701.filter (fun n ↦ n ≤ 2381)

/-- Select the first certified weight endpoint at or above an index. -/
def target028Cell37RowFor (n : ℕ) : Target028GeneralWeightRow :=
  (target028Cell37Rows.find? (fun r ↦ n ≤ r.b)).getD
    ⟨2381, 2381, 0, -2, 2, 2838, 48796, 58542634, 1823⟩

/-- Rational lower weight selected for a retained prime-power index. -/
def target028Cell37Weight (n : ℕ) : ℚ :=
  ((target028Cell37RowFor n).weight : ℚ) / 1000000

-- Kernel reduction traverses the existing 193-row prime-power table.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each selected index is matched with the finite table of endpoints.
/-- Each retained prime power has a checked endpoint and a valid monotone range. -/
theorem target028_cell37_select :
    ∀ n ∈ target028Cell37Prefix,
      1 ≤ n ∧
        target028Cell37RowFor n ∈ target028Cell37Rows ∧
        n ≤ (target028Cell37RowFor n).b ∧
        (11 ≤ n ∨ n = (target028Cell37RowFor n).b) ∧ (target028Cell37RowFor n).cut = 2381 := by
  decide +kernel

-- The selected rational contributions are reduced by the kernel.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The prefix uses the previously checked prime-power logarithm data.
/-- The rational principal prefix exceeds the cell's lower endpoint. -/
theorem target028_cell37_sum_check :
    (62557 / 5000 : ℚ) <
      ∑ n ∈ target028Cell37Prefix,
        refinedPsiLower n (target028EulerData2701 n) * target028Cell37Weight n := by
  decide +kernel

-- Applying the certified prime-power prefix traverses its finite definition.
set_option maxRecDepth 1000000 in
/-- The actual finite principal sum exceeds the checked rational lower bound. -/
theorem target028_cell37_principal :
    (62557 / 5000 : ℝ) <
      ∑ n ∈ Finset.Ioc 0 ⌊(2381 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 2381 n).re := by
  have hs : target028Cell37Prefix ⊆ target028EulerSet2701 := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have ht : target028Cell37Prefix ⊆ Finset.Ioc 0 ⌊(2381 : ℝ)⌋₊ := by
    intro n hn
    have h := target028_cell37_select n hn
    simp only [Nat.floor_ofNat, Finset.mem_Ioc]
    exact ⟨Nat.lt_of_lt_of_le (by decide) h.1, (Finset.mem_filter.mp hn).2⟩
  have hw0 : ∀ n ∈ target028Cell37Prefix, 0 ≤ target028Cell37Weight n := by
    intro n hn
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hw :
    ∀ n ∈ target028Cell37Prefix, (target028Cell37Weight n : ℝ) ≤ refinedScaledWeight 2381 n := by
    intro n hn
    obtain ⟨hn1, hm, hnb, hsplit, hcut⟩ := target028_cell37_select n hn
    have hcheck := target028_cell37_rows_check (target028Cell37RowFor n) hm
    have hrow := (target028Cell37RowFor n).sound hcheck
    rw [hcut] at hrow
    have hb : (target028Cell37RowFor n).b ≤ 2381 := by
      have h := hcheck
      simp only [Target028GeneralWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at h
      simpa only [hcut] using h.2.2.1
    have hweight :
      refinedScaledWeight 2381 (target028Cell37RowFor n).b ≤ refinedScaledWeight 2381 n := by
      rcases hsplit with hlarge | heq
      · exact
          target028_weight_antitone_finite (by exact_mod_cast hlarge) (by exact_mod_cast hnb)
            (by exact_mod_cast hb) (by norm_num only)
      · exact
          le_of_eq (congrArg (refinedScaledWeight 2381) (congrArg (fun k : ℕ ↦ (k : ℝ)) heq.symm))
    simpa only [target028Cell37Weight, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hrow.trans hweight
  have hl :=
    target028_principal_checked_rows (by norm_num only : (0 : ℝ) < 2381) target028Cell37Prefix
      target028EulerData2701 target028Cell37Weight (fun n hn ↦ target028_euler2701_check n (hs hn))
      ht hw0 hw
  have hr :
    ((62557 / 5000 : ℚ) : ℝ) <
      ((∑ n ∈ target028Cell37Prefix,
            refinedPsiLower n (target028EulerData2701 n) * target028Cell37Weight n :
          ℚ) :
        ℝ) :=
    Rat.cast_lt.mpr target028_cell37_sum_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr.trans_le hl

/-- The certified upper budget at the cell endpoint is at most four times
the rational principal lower bound. All comparisons use rational arithmetic. -/
theorem target028_cell37_budget :
    target028MomentBudget 2381 (94225 / 1000) ≤ 4 * (62557 / 5000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 2381 11 32 0 (15551 / 2000) = true from by
          decide +kernel)).2
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 2381 0 (112739 / 500000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hpow
  have hl : Real.log 2381 ≤ (15551 / 2000 : ℝ) := by
    norm_num only at hlog ⊢; exact hlog
  have hp : (2381 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (112739 / 500000000 : ℝ) := by
    norm_num only at hpow ⊢
    exact hpow
  have hs : (24397 / 500 : ℝ) ≤ Real.sqrt 2381 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 2381 ≤ (48797 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hb :=
    target028_budget_envelope (X := 2381) (U := 94225 / 1000) (L := 15551 / 2000) (P :=
      112739 / 500000000) (s := 24397 / 500) (t := 48797 / 1000) (by norm_num only)
      (by norm_num only) hl hp (by norm_num only) hs ht
  apply hb.trans
  norm_num only [target028BudgetEnvelope, target028MomentPolynomial]

/-- A uniform three-prime Korselt product in this logarithmic cell has a
0.28 rejecting prime. The cutoff, finite principal sum, and budget are all
verified at the cell endpoints. -/
theorem target028_cell37_pair {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (92225 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 94225 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (2381 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 2381) (U := 94225 / 1000) (S := 62557 / 5000) (by norm_num only) hU hcut
      (le_of_lt target028_cell37_principal) target028_cell37_budget

end PseudoPrime.PrimeTestBounds.MillerRabin
