/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.ExplicitFiniteFiberCounts
public import PseudoPrime.NumberTheory.Heilbronn.DoubleExponentialBudgets

/-! # Numerical magnitude budgets for precision 136 -/

public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- A degree coefficient is bounded by 2^(2^B) whenever the prescribed
moment order is at least four and its combined inner exponent fits B.
Apply the symbolic quotient and power budgets before specializing B to
a large closed natural number, avoiding kernel evaluation of that number. -/
theorem fiberBandCoefficient_le_double_exp_of_order_budget {m c B : ℕ}
    (hr : 4 ≤ fiberBandMomentOrder m c)
    (hbudget : 4 * fiberBandMomentOrder m c + (fiberBandGrowthOrder m c) ^ 2 * (m - 1) + 4 ≤ B) :
    fiberBandCoefficient m c ≤ 2 ^ (2 ^ B) := by
  have hQ := quotientPowerBoundConstant_le_double_exp hr
  have hD := pow_le_double_exp_add hQ ((fiberBandGrowthOrder m c) ^ 2 * (m - 1))
  have hC := band_coefficient_le_double_exp hD
  exact
    hC.trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.pow_le_pow_right (by decide : 0 < 2) hbudget))

/-- Apply the logarithmic quotient coefficient bound to a prescribed
moment order. The combined exponent includes 2r, the bit length of
2r (log2(2r) + 1) + 2r, the growth-order power, and four units for the
band coefficient. -/
theorem fiberBandCoefficient_le_double_exp_of_log_order_budget_sharp {m c B : ℕ}
    (hr : 4 ≤ fiberBandMomentOrder m c)
    (hbudget :
      2 * fiberBandMomentOrder m c +
          Nat.log2
            (2 * fiberBandMomentOrder m c * (Nat.log2 (2 * fiberBandMomentOrder m c) + 1) +
              2 * fiberBandMomentOrder m c) +
          (fiberBandGrowthOrder m c) ^ 2 * (m - 1) +
          4 ≤
        B) :
    fiberBandCoefficient m c ≤ 2 ^ (2 ^ B) := by
  have hQ := quotientPowerBoundConstant_le_double_exp_log hr
  have hD := pow_le_double_exp_add hQ ((fiberBandGrowthOrder m c) ^ 2 * (m - 1))
  have hC := band_coefficient_le_double_exp hD
  have hbudget' :
    (2 * fiberBandMomentOrder m c +
          Nat.log2
            (2 * fiberBandMomentOrder m c * (Nat.log2 (2 * fiberBandMomentOrder m c) + 1) +
              2 * fiberBandMomentOrder m c) +
          (fiberBandGrowthOrder m c) ^ 2 * (m - 1)) +
        4 ≤
      B := by
    nlinarith only [hbudget]
  exact
    hC.trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.pow_le_pow_right (by decide : 0 < 2) hbudget'))

/-- Apply the quarter-range quotient estimate when the moment order is at least
seven. The reduced coefficient budget saves one unit in its first exponent term. -/
theorem fiberBandCoefficient_le_double_exp_of_log_order_budget_quarter {m c B : ℕ}
    (hr : 7 ≤ fiberBandMomentOrder m c)
    (hbudget :
      2 * fiberBandMomentOrder m c - 1 +
          Nat.log2
            (2 * fiberBandMomentOrder m c * (Nat.log2 (2 * fiberBandMomentOrder m c) + 1) +
              2 * fiberBandMomentOrder m c) +
          (fiberBandGrowthOrder m c) ^ 2 * (m - 1) +
          4 ≤
        B) :
    fiberBandCoefficient m c ≤ 2 ^ (2 ^ B) := by
  have hQ := quotientPowerBoundConstant_le_double_exp_log_quarter hr
  have hD := pow_le_double_exp_add hQ ((fiberBandGrowthOrder m c) ^ 2 * (m - 1))
  have hC := band_coefficient_le_double_exp hD
  exact
    hC.trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.pow_le_pow_right (by decide : 0 < 2) hbudget))

/-- Preserve the original logarithmic-budget interface with one spare unit.
The sharper coefficient estimate removes that unit internally, so existing
precision budgets continue to use the same hypothesis. -/
theorem fiberBandCoefficient_le_double_exp_of_log_order_budget {m c B : ℕ}
    (hr : 4 ≤ fiberBandMomentOrder m c)
    (hbudget :
      2 * fiberBandMomentOrder m c +
          Nat.log2
            (2 * fiberBandMomentOrder m c * (Nat.log2 (2 * fiberBandMomentOrder m c) + 1) +
              2 * fiberBandMomentOrder m c) +
          1 +
          (fiberBandGrowthOrder m c) ^ 2 * (m - 1) +
          4 ≤
        B) :
    fiberBandCoefficient m c ≤ 2 ^ (2 ^ B) := by
  apply fiberBandCoefficient_le_double_exp_of_log_order_budget_sharp hr
  nlinarith only [hbudget]

/-- For degrees 2≤m≤42 at precision 136, the growth order is at most
two million, the moment order lies in [4,10^20), and its coefficient power
is below 10^15. Use monotonic natural products; no factorial is evaluated. -/
theorem fiberBand_orders_136_bounds {m : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42) :
    fiberBandGrowthOrder m 136 ≤ 2000000 ∧
      4 ≤ fiberBandMomentOrder m 136 ∧
      fiberBandMomentOrder m 136 < 10 ^ 20 ∧
      (fiberBandGrowthOrder m 136) ^ 2 * (m - 1) < 10 ^ 15 := by
  have hm1 : m - 1 ≤ 41 := Nat.sub_le_sub_right hhi 1
  have hn : fiberBandGrowthOrder m 136 ≤ 2000000 := by
    simp only [fiberBandGrowthOrder, ite_eq_right (by norm_num only : 136 ≠ 20)]
    nlinarith only [hm1]
  have hn2 := Nat.pow_le_pow_left hn 2
  have he := Nat.mul_le_mul hn2 hm1
  have hrup : fiberBandMomentOrder m 136 ≤ 4 * 136 * 2000000 ^ 2 * 41 + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_left (4 * 136) hn2) hm1) 1
  have hmlow : 1 ≤ m - 1 := by
    have h := Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans hlo)
    nlinarith only [h, hlo]
  have hnpow : 1 ≤ (fiberBandGrowthOrder m 136) ^ 2 :=
    Nat.one_le_pow _ _ (fiberBandGrowthOrder_pos m 136)
  have hrlo := Nat.mul_le_mul_left (4 * 136) (Nat.mul_le_mul hnpow hmlow)
  refine ⟨hn, ?_, ?_, ?_⟩
  · change 4 ≤ 4 * 136 * (fiberBandGrowthOrder m 136) ^ 2 * (m - 1) + 1
    nlinarith only [hrlo]
  · exact hrup.trans_lt (by norm_num only)
  · exact he.trans_lt (by norm_num only)

/-- For degrees m≤42 at precision 136, use the logarithmic factorial bound
to obtain common inner-exponent budget 1,388,714,676,973. -/
theorem fiberBand_orders_136_improved_budget {m : ℕ} (hhi : m ≤ 42) :
    2 * fiberBandMomentOrder m 136 +
        Nat.log2
          (2 * fiberBandMomentOrder m 136 * (Nat.log2 (2 * fiberBandMomentOrder m 136) + 1) +
            2 * fiberBandMomentOrder m 136) +
        1 +
        (fiberBandGrowthOrder m 136) ^ 2 * (m - 1) +
        4 ≤
      1388714676973 := by
  have hm1 : m - 1 ≤ 41 := Nat.sub_le_sub_right hhi 1
  have hg : fiberBandGrowthOrder m 136 ≤ 5577 := by
    simp only [fiberBandGrowthOrder, ite_eq_right (by norm_num only : 136 ≠ 20)]
    nlinarith only [hm1]
  have hg2 := Nat.pow_le_pow_left hg 2
  have hprod := Nat.mul_le_mul hg2 hm1
  have he : (fiberBandGrowthOrder m 136) ^ 2 * (m - 1) ≤ 1275220089 := by
    calc
      _ ≤ 5577 ^ 2 * 41 := hprod
      _ ≤ 1275220089 := by norm_num only
  have hr : fiberBandMomentOrder m 136 ≤ 693719728417 := by
    simp only [fiberBandMomentOrder, ite_eq_right (by norm_num only : 136 ≠ 20)]
    nlinarith only [he]
  have hlogP :
    Nat.log2
          (2 * fiberBandMomentOrder m 136 * (Nat.log2 (2 * fiberBandMomentOrder m 136) + 1) +
            2 * fiberBandMomentOrder m 136) +
        1 ≤
      46 := by
    have h2r : 2 * fiberBandMomentOrder m 136 < 2 ^ 41 := by
      calc
        _ ≤ 2 * 693719728417 := Nat.mul_le_mul_left 2 hr
        _ < 2 ^ 41 := by norm_num only
    have hlog2r : Nat.log2 (2 * fiberBandMomentOrder m 136) < 41 := by
      rw [Nat.log2_eq_log_two]
      exact
        Nat.log_lt_of_lt_pow
          (Nat.ne_of_gt (Nat.mul_pos (by decide) (fiberBandMomentOrder_pos m 136))) h2r
    have hlog2r' : Nat.log2 (2 * fiberBandMomentOrder m 136) + 1 ≤ 41 := Nat.succ_le_iff.mpr hlog2r
    have hmul := Nat.mul_le_mul_left (2 * fiberBandMomentOrder m 136) hlog2r'
    have hP :
      2 * fiberBandMomentOrder m 136 * (Nat.log2 (2 * fiberBandMomentOrder m 136) + 1) +
          2 * fiberBandMomentOrder m 136 <
        2 ^ 46 := by
      calc
        _ ≤ 2 * fiberBandMomentOrder m 136 * 41 + 2 * fiberBandMomentOrder m 136 :=
          Nat.add_le_add_right hmul _
        _ ≤ 84 * 693719728417 := by nlinarith only [hr]
        _ < 2 ^ 46 := by norm_num only
    have hPpos :
      0 <
        2 * fiberBandMomentOrder m 136 * (Nat.log2 (2 * fiberBandMomentOrder m 136) + 1) +
          2 * fiberBandMomentOrder m 136 := by
      have hterm : 0 < 2 * fiberBandMomentOrder m 136 :=
        Nat.mul_pos (by decide) (fiberBandMomentOrder_pos m 136)
      have hnonneg :
        0 ≤ 2 * fiberBandMomentOrder m 136 * (Nat.log2 (2 * fiberBandMomentOrder m 136) + 1) :=
        Nat.zero_le _
      nlinarith only [hterm, hnonneg]
    have hlogP' :
      Nat.log2
          (2 * fiberBandMomentOrder m 136 * (Nat.log2 (2 * fiberBandMomentOrder m 136) + 1) +
            2 * fiberBandMomentOrder m 136) <
        46 := by
      rw [Nat.log2_eq_log_two]
      exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hPpos) hP
    exact Nat.succ_le_iff.mpr hlogP'
  nlinarith only [hr, he, hlogP]

/-- Each degree 2≤m≤42 at precision 136 has coefficient at most
2^(2^1388714676973). Use the logarithmic quotient bound and exact orders. -/
theorem fiberBandCoefficient_136_le_double_exp {m : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42) :
    fiberBandCoefficient m 136 ≤ 2 ^ (2 ^ 1388714676973) := by
  have hrlo : 4 ≤ fiberBandMomentOrder m 136 := (fiberBand_orders_136_bounds hlo hhi).2.1
  apply fiberBandCoefficient_le_double_exp_of_log_order_budget hrlo
  exact fiberBand_orders_136_improved_budget hhi

/-- At precision 80, every degree coefficient through degree 42 fits the
common double-exponential budget with inner exponent 283 billion. The bound
uses the explicit logarithmic factorial estimate at each degree. -/
theorem fiberBand_orders_80_improved_budget {m : ℕ} (hhi : m ≤ 42) :
    2 * fiberBandMomentOrder m 80 +
        Nat.log2
          (2 * fiberBandMomentOrder m 80 * (Nat.log2 (2 * fiberBandMomentOrder m 80) + 1) +
            2 * fiberBandMomentOrder m 80) +
        1 +
        (fiberBandGrowthOrder m 80) ^ 2 * (m - 1) +
        4 ≤
      283000000000 := by
  have hm1 : m - 1 ≤ 41 := Nat.sub_le_sub_right hhi 1
  have hg : fiberBandGrowthOrder m 80 ≤ 3281 := by
    simp only [fiberBandGrowthOrder, ite_eq_right (by norm_num only : 80 ≠ 20)]
    nlinarith only [hm1]
  have hg2 := Nat.pow_le_pow_left hg 2
  have hprod := Nat.mul_le_mul hg2 hm1
  have he : (fiberBandGrowthOrder m 80) ^ 2 * (m - 1) ≤ 441363401 := by
    calc
      _ ≤ 3281 ^ 2 * 41 := hprod
      _ ≤ 441363401 := by norm_num only
  have hr : fiberBandMomentOrder m 80 ≤ 141236288321 := by
    simp only [fiberBandMomentOrder, ite_eq_right (by norm_num only : 80 ≠ 20)]
    calc
      _ ≤ 4 * 80 * 3281 ^ 2 * 41 + 1 := by
        apply Nat.add_le_add_right
        exact Nat.mul_le_mul (Nat.mul_le_mul_left (4 * 80) hg2) hm1
      _ ≤ 141236288321 := by norm_num only
  have h2r : 2 * fiberBandMomentOrder m 80 < 2 ^ 39 := by
    calc
      _ ≤ 2 * 141236288321 := Nat.mul_le_mul_left 2 hr
      _ < 2 ^ 39 := by norm_num only
  have hlog2r : Nat.log2 (2 * fiberBandMomentOrder m 80) < 39 := by
    rw [Nat.log2_eq_log_two]
    exact
      Nat.log_lt_of_lt_pow (Nat.ne_of_gt (Nat.mul_pos (by decide) (fiberBandMomentOrder_pos m 80)))
        h2r
  have hlog2r' : Nat.log2 (2 * fiberBandMomentOrder m 80) + 1 ≤ 39 := Nat.succ_le_iff.mpr hlog2r
  have hmul := Nat.mul_le_mul_left (2 * fiberBandMomentOrder m 80) hlog2r'
  have hP :
    2 * fiberBandMomentOrder m 80 * (Nat.log2 (2 * fiberBandMomentOrder m 80) + 1) +
        2 * fiberBandMomentOrder m 80 <
      2 ^ 45 := by
    calc
      _ ≤ 2 * fiberBandMomentOrder m 80 * 39 + 2 * fiberBandMomentOrder m 80 :=
        Nat.add_le_add_right hmul _
      _ ≤ 80 * 141236288321 := by nlinarith only [hr]
      _ < 2 ^ 45 := by norm_num only
  have hPpos :
    0 <
      2 * fiberBandMomentOrder m 80 * (Nat.log2 (2 * fiberBandMomentOrder m 80) + 1) +
        2 * fiberBandMomentOrder m 80 := by
    have hterm : 0 < 2 * fiberBandMomentOrder m 80 :=
      Nat.mul_pos (by decide) (fiberBandMomentOrder_pos m 80)
    have hnonneg :
      0 ≤ 2 * fiberBandMomentOrder m 80 * (Nat.log2 (2 * fiberBandMomentOrder m 80) + 1) :=
      Nat.zero_le _
    nlinarith only [hterm, hnonneg]
  have hlogP' :
    Nat.log2
        (2 * fiberBandMomentOrder m 80 * (Nat.log2 (2 * fiberBandMomentOrder m 80) + 1) +
          2 * fiberBandMomentOrder m 80) <
      45 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hPpos) hP
  have hlogP :
    Nat.log2
          (2 * fiberBandMomentOrder m 80 * (Nat.log2 (2 * fiberBandMomentOrder m 80) + 1) +
            2 * fiberBandMomentOrder m 80) +
        1 ≤
      45 :=
    Nat.succ_le_iff.mpr hlogP'
  nlinarith only [hr, he, hlogP]

/-- At precision 80, all eight required degree coefficients are at most
2^(2^283000000000). Use the logarithmic quotient coefficient estimate. -/
theorem fiberBandCoefficient_80_le_double_exp {m : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42) :
    fiberBandCoefficient m 80 ≤ 2 ^ (2 ^ 283000000000) := by
  have hrlo : 4 ≤ fiberBandMomentOrder m 80 := by
    have hm1 : 1 ≤ m - 1 := Nat.sub_le_sub_right hlo 1
    have hbase : 1 ≤ 80 * (m - 1) + 1 := by nlinarith only [hm1]
    have hpow : 1 ≤ (80 * (m - 1) + 1) ^ 2 := Nat.one_le_pow _ _ hbase
    have hprod : 1 ≤ (80 * (m - 1) + 1) ^ 2 * (m - 1) := Nat.mul_le_mul hpow hm1
    have hprod' : 1 ≤ (80 * (m - 1) + 1) ^ 2 * (m - 1) := by
      simpa only [fiberBandGrowthOrder, ite_eq_right (by norm_num only : 80 ≠ 20)] using hprod
    simp only [fiberBandMomentOrder, fiberBandGrowthOrder,
      ite_eq_right (by norm_num only : 80 ≠ 20)]
    nlinarith only [hprod']
  exact
    fiberBandCoefficient_le_double_exp_of_log_order_budget hrlo
      (fiberBand_orders_80_improved_budget hhi)

/-- A common bound 2^(2^B) for all eight degree coefficients gives
2^(2^(B+4)) for their sum plus one. Compare sums before absorbing a
factor sixteen, with B left symbolic throughout the arithmetic proof. -/
theorem eightDegreeFiberCoefficient_le_double_exp_of_degree_bounds {c B : ℕ}
    (hF : ∀ m ∈ ({6, 7, 8, 9, 11, 14, 21, 42} : Finset ℕ), fiberBandCoefficient m c ≤ 2 ^ (2 ^ B)) :
    eightDegreeFiberCoefficient c ≤ 2 ^ (2 ^ (B + 4)) := by
  let D : Finset ℕ := {6, 7, 8, 9, 11, 14, 21, 42}
  have hU : 1 ≤ (2 : ℕ) ^ (2 ^ B) := Nat.one_le_pow _ _ (by decide)
  have hs :=
    one_add_sum_le_card_budget D (fun m ↦ fiberBandCoefficient m c) (k := 8) (by decide) hU hF
  have hK : eightDegreeFiberCoefficient c ≤ 16 * 2 ^ (2 ^ B) :=
    hs.trans (Nat.mul_le_mul_right _ (by decide : 8 + 1 ≤ 16))
  exact hK.trans (mul_le_double_exp_add (A := 16) (k := 4) (by decide))

/-- If the eight degree coefficients share the bound 2^(2^B) and B≥2,
their sum plus one is below 2^(2^(B+1)). Use the exact factor nine and
absorb it into the square of the double-exponential unit. -/
theorem eightDegreeFiberCoefficient_le_double_exp_succ_of_degree_bounds {c B : ℕ} (hB : 2 ≤ B)
    (hF : ∀ m ∈ ({6, 7, 8, 9, 11, 14, 21, 42} : Finset ℕ), fiberBandCoefficient m c ≤ 2 ^ (2 ^ B)) :
    eightDegreeFiberCoefficient c ≤ 2 ^ (2 ^ (B + 1)) := by
  let D : Finset ℕ := {6, 7, 8, 9, 11, 14, 21, 42}
  let U : ℕ := 2 ^ (2 ^ B)
  have hU : 1 ≤ U := Nat.one_le_pow _ _ (by decide : 0 < 2)
  have hF' : ∀ m ∈ D, fiberBandCoefficient m c ≤ U := by
    intro m hm
    exact hF m (by simpa only [D] using hm)
  have hs :=
    one_add_sum_le_card_budget D (fun m ↦ fiberBandCoefficient m c) (k := 8) (by decide) hU hF'
  have hK : eightDegreeFiberCoefficient c ≤ 9 * U := by
    change 1 + ∑ m ∈ D, fiberBandCoefficient m c ≤ 9 * U
    exact hs
  have h2B : 4 ≤ 2 ^ B := Nat.pow_le_pow_right (by decide : 0 < 2) hB
  have hU16 : 2 ^ 4 ≤ U := by
    dsimp only [U]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) h2B
  have h9 : 9 < U := by
    calc
      9 < 2 ^ 4 := by norm_num only
      _ ≤ U := hU16
  exact hK.trans (mul_lt_double_exp_succ h9).le

/-- The finite-fiber coefficient 4(2a+1) times the eight-degree sum is
below 2^(2^(B+1)) when each degree coefficient is at most 2^(2^B) and
36(2a+1) is smaller than that unit. Retain the factor nine from the sum
instead of separately rounding the degree and harmonic factors. -/
theorem finiteFiberCountCoefficient_lt_double_exp_of_degree_bounds {c a B : ℕ}
    (hfactor : 36 * (2 * a + 1) < 2 ^ (2 ^ B))
    (hF : ∀ m ∈ ({6, 7, 8, 9, 11, 14, 21, 42} : Finset ℕ), fiberBandCoefficient m c ≤ 2 ^ (2 ^ B)) :
    finiteFiberCountCoefficient c a < 2 ^ (2 ^ (B + 1)) := by
  let D : Finset ℕ := {6, 7, 8, 9, 11, 14, 21, 42}
  let U : ℕ := 2 ^ (2 ^ B)
  have hU : 1 ≤ U := Nat.one_le_pow _ _ (by decide : 0 < 2)
  have hF' : ∀ m ∈ D, fiberBandCoefficient m c ≤ U := by
    intro m hm
    exact hF m (by simpa only [D] using hm)
  have hs :=
    one_add_sum_le_card_budget D (fun m ↦ fiberBandCoefficient m c) (k := 8) (by decide) hU hF'
  have hK : eightDegreeFiberCoefficient c ≤ 9 * U := by
    change 1 + ∑ m ∈ D, fiberBandCoefficient m c ≤ 9 * U
    exact hs
  have hC : finiteFiberCountCoefficient c a ≤ (36 * (2 * a + 1)) * U := by
    unfold finiteFiberCountCoefficient
    calc
      _ = (4 * (2 * a + 1)) * eightDegreeFiberCoefficient c := by ring
      _ ≤ (4 * (2 * a + 1)) * (9 * U) := Nat.mul_le_mul_left _ hK
      _ = (36 * (2 * a + 1)) * U := by ring
  exact hC.trans_lt (mul_lt_double_exp_succ hfactor)

/-- The fixed harmonic multiplier 5796 is smaller than the double-exponential
unit whenever its inner index is at least four. Keep this argument generic so
specializing the index does not ask the kernel to evaluate a huge power. -/
theorem finiteFiberCount_harmonic_factor_lt_unit {B : ℕ} (hB : 4 ≤ B) : 5796 < 2 ^ (2 ^ B) := by
  have h2B : 16 ≤ 2 ^ B := Nat.pow_le_pow_right (by decide : 0 < 2) hB
  have hU16 : 2 ^ 16 ≤ 2 ^ (2 ^ B) := Nat.pow_le_pow_right (by decide : 0 < 2) h2B
  calc
    5796 < 2 ^ 16 := by norm_num only
    _ ≤ 2 ^ (2 ^ B) := hU16

/-- The eight-degree coefficient at precision 136 is at most
2^(2^(1388714676973+1)). Bound each degree coefficient and absorb their sum. -/
theorem eightDegreeFiberCoefficient_136_le_double_exp :
    eightDegreeFiberCoefficient 136 ≤ 2 ^ (2 ^ (1388714676973 + 1)) := by
  apply eightDegreeFiberCoefficient_le_double_exp_succ_of_degree_bounds (by decide)
  intro m hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h | h | h | h | h
  all_goals subst m; exact fiberBandCoefficient_136_le_double_exp (by decide) (by decide)

/-- If the degree sum fits 2^(2^B), its harmonic multiplier fits 2^k,
and B+k<B', the full count coefficient is smaller than 2^(2^B').
Collect the natural product and apply symbolic double-exponential budgets.
This permits closed numerical specialization without evaluating towers. -/
theorem finiteFiberCountCoefficient_lt_double_exp_of_budget {c a B B' k : ℕ}
    (hK : eightDegreeFiberCoefficient c ≤ 2 ^ (2 ^ B)) (hscale : 4 * (2 * a + 1) ≤ 2 ^ k)
    (hgap : B + k < B') : finiteFiberCountCoefficient c a < 2 ^ (2 ^ B') := by
  have h : finiteFiberCountCoefficient c a ≤ (4 * (2 * a + 1)) * 2 ^ (2 ^ B) := by
    unfold finiteFiberCountCoefficient
    calc
      _ = (4 * (2 * a + 1)) * eightDegreeFiberCoefficient c := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hK
  have h' := h.trans (mul_le_double_exp_add hscale)
  exact
    h'.trans_lt
      (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.pow_lt_pow_right (by decide : 1 < 2) hgap))

/-- The explicit full count coefficient at a=68,c=136 is smaller
than 2^(2^(1388714676973+1)). Combine the degree-sum factor nine and the
harmonic factor 4932 before absorbing them into the double-exponential unit. -/
theorem finiteFiberCountCoefficient_136_68_lt_double_exp :
    finiteFiberCountCoefficient 136 68 < 2 ^ (2 ^ (1388714676973 + 1)) := by
  apply finiteFiberCountCoefficient_lt_double_exp_of_degree_bounds
  · calc
      36 * (2 * 68 + 1) = 4932 := by norm_num only
      _ < 5796 := by norm_num only
      _ < 2 ^ (2 ^ 1388714676973) :=
        finiteFiberCount_harmonic_factor_lt_unit (B := 1388714676973) (by decide)
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h | h | h | h | h | h
    all_goals subst m; exact fiberBandCoefficient_136_le_double_exp (by decide) (by decide)

/-- The explicit full count coefficient at a=40,c=80 is below
2^(2^(283000000000+1)). Combine the degree-sum and harmonic factors before
absorbing them into the double-exponential unit. -/
theorem finiteFiberCountCoefficient_80_40_lt_double_exp :
    finiteFiberCountCoefficient 80 40 < 2 ^ (2 ^ (283000000000 + 1)) := by
  apply finiteFiberCountCoefficient_lt_double_exp_of_degree_bounds
  · calc
      36 * (2 * 40 + 1) = 2916 := by norm_num only
      _ < 5796 := by norm_num only
      _ < 2 ^ (2 ^ 283000000000) :=
        finiteFiberCount_harmonic_factor_lt_unit (B := 283000000000)
          (by norm_num only : (4 : ℕ) ≤ 283000000000)
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h | h | h | h | h | h
    all_goals subst m;
              exact fiberBandCoefficient_80_le_double_exp (by norm_num only) (by norm_num only)

/-- At precision 76, every degree coefficient through degree 42 fits the
common double-exponential budget with inner exponent 242591038692. -/
theorem fiberBand_orders_76_improved_budget {m : ℕ} (hhi : m ≤ 42) :
    2 * fiberBandMomentOrder m 76 +
        Nat.log2
          (2 * fiberBandMomentOrder m 76 * (Nat.log2 (2 * fiberBandMomentOrder m 76) + 1) +
            2 * fiberBandMomentOrder m 76) +
        1 +
        (fiberBandGrowthOrder m 76) ^ 2 * (m - 1) +
        4 ≤
      242591038692 := by
  have hm1 : m - 1 ≤ 41 := Nat.sub_le_sub_right hhi 1
  have hg : fiberBandGrowthOrder m 76 ≤ 3117 := by
    simp only [fiberBandGrowthOrder, ite_eq_right (by norm_num only : 76 ≠ 20)]
    nlinarith only [hm1]
  have hg2 := Nat.pow_le_pow_left hg 2
  have hprod := Nat.mul_le_mul hg2 hm1
  have he : (fiberBandGrowthOrder m 76) ^ 2 * (m - 1) ≤ 398343249 := by
    calc
      _ ≤ 3117 ^ 2 * 41 := hprod
      _ ≤ 398343249 := by norm_num only
  have hr : fiberBandMomentOrder m 76 ≤ 121096347697 := by
    simp only [fiberBandMomentOrder, ite_eq_right (by norm_num only : 76 ≠ 20)]
    calc
      _ ≤ 4 * 76 * 3117 ^ 2 * 41 + 1 := by
        apply Nat.add_le_add_right
        exact Nat.mul_le_mul (Nat.mul_le_mul_left (4 * 76) hg2) hm1
      _ ≤ 121096347697 := by norm_num only
  have h2r : 2 * fiberBandMomentOrder m 76 < 2 ^ 39 := by
    calc
      _ ≤ 2 * 121096347697 := Nat.mul_le_mul_left 2 hr
      _ < 2 ^ 39 := by norm_num only
  have hlog2r : Nat.log2 (2 * fiberBandMomentOrder m 76) < 39 := by
    rw [Nat.log2_eq_log_two]
    exact
      Nat.log_lt_of_lt_pow (Nat.ne_of_gt (Nat.mul_pos (by decide) (fiberBandMomentOrder_pos m 76)))
        h2r
  have hlog2r' : Nat.log2 (2 * fiberBandMomentOrder m 76) + 1 ≤ 39 := Nat.succ_le_iff.mpr hlog2r
  have hmul := Nat.mul_le_mul_left (2 * fiberBandMomentOrder m 76) hlog2r'
  have hP :
    2 * fiberBandMomentOrder m 76 * (Nat.log2 (2 * fiberBandMomentOrder m 76) + 1) +
        2 * fiberBandMomentOrder m 76 <
      2 ^ 45 := by
    calc
      _ ≤ 2 * fiberBandMomentOrder m 76 * 39 + 2 * fiberBandMomentOrder m 76 :=
        Nat.add_le_add_right hmul _
      _ ≤ 80 * 121096347697 := by nlinarith only [hr]
      _ < 2 ^ 45 := by norm_num only
  have hPpos :
    0 <
      2 * fiberBandMomentOrder m 76 * (Nat.log2 (2 * fiberBandMomentOrder m 76) + 1) +
        2 * fiberBandMomentOrder m 76 := by
    have hterm : 0 < 2 * fiberBandMomentOrder m 76 :=
      Nat.mul_pos (by decide) (fiberBandMomentOrder_pos m 76)
    have hnonneg :
      0 ≤ 2 * fiberBandMomentOrder m 76 * (Nat.log2 (2 * fiberBandMomentOrder m 76) + 1) :=
      Nat.zero_le _
    nlinarith only [hterm, hnonneg]
  have hlogP' :
    Nat.log2
        (2 * fiberBandMomentOrder m 76 * (Nat.log2 (2 * fiberBandMomentOrder m 76) + 1) +
          2 * fiberBandMomentOrder m 76) <
      45 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hPpos) hP
  have hlogP :
    Nat.log2
          (2 * fiberBandMomentOrder m 76 * (Nat.log2 (2 * fiberBandMomentOrder m 76) + 1) +
            2 * fiberBandMomentOrder m 76) +
        1 ≤
      45 :=
    Nat.succ_le_iff.mpr hlogP'
  nlinarith only [hr, he, hlogP]

/-- Each degree 2≤m≤42 at precision 76 has coefficient at most
2^(2^242591038692). -/
theorem fiberBandCoefficient_76_le_double_exp {m : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42) :
    fiberBandCoefficient m 76 ≤ 2 ^ (2 ^ 242591038692) := by
  have hgpos : 1 ≤ fiberBandGrowthOrder m 76 := Nat.succ_le_iff.mpr (fiberBandGrowthOrder_pos m 76)
  have hm1 : 1 ≤ m - 1 := Nat.sub_le_sub_right hlo 1
  have hprod : 1 ≤ fiberBandGrowthOrder m 76 ^ 2 * (m - 1) :=
    Nat.mul_le_mul (Nat.one_le_pow _ _ hgpos) hm1
  have hrlo : 4 ≤ fiberBandMomentOrder m 76 := by
    have hprod' : 1 ≤ (76 * (m - 1) + 1) ^ 2 * (m - 1) := by
      simpa only [fiberBandGrowthOrder, ite_eq_right (by norm_num only : 76 ≠ 20)] using hprod
    simp only [fiberBandMomentOrder, fiberBandGrowthOrder,
      ite_eq_right (by norm_num only : 76 ≠ 20)]
    nlinarith only [hprod']
  apply fiberBandCoefficient_le_double_exp_of_log_order_budget hrlo
  exact fiberBand_orders_76_improved_budget hhi

/-- The full count coefficient at a=38,c=76 is below
2^(2^(242591038692+1)). Combine the degree-sum and harmonic factors first. -/
theorem finiteFiberCountCoefficient_76_38_lt_double_exp :
    finiteFiberCountCoefficient 76 38 < 2 ^ (2 ^ (242591038692 + 1)) := by
  apply finiteFiberCountCoefficient_lt_double_exp_of_degree_bounds
  · calc
      36 * (2 * 38 + 1) = 2772 := by norm_num only
      _ < 5796 := by norm_num only
      _ < 2 ^ (2 ^ 242591038692) :=
        finiteFiberCount_harmonic_factor_lt_unit (B := 242591038692)
          (by norm_num only : (4 : ℕ) ≤ 242591038692)
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h | h | h | h | h | h
    all_goals subst m; exact fiberBandCoefficient_76_le_double_exp (by decide) (by decide)

/-- For degrees m≤42 at precision 64, the logarithmic quotient budget is
below 145,000,000,000. Bound growth and moment orders before taking log2. -/
theorem fiberBand_orders_64_improved_budget {m : ℕ} (hhi : m ≤ 42) :
    2 * fiberBandMomentOrder m 64 +
        Nat.log2
          (2 * fiberBandMomentOrder m 64 * (Nat.log2 (2 * fiberBandMomentOrder m 64) + 1) +
            2 * fiberBandMomentOrder m 64) +
        1 +
        (fiberBandGrowthOrder m 64) ^ 2 * (m - 1) +
        4 ≤
      145000000000 := by
  have hm1 : m - 1 ≤ 41 := Nat.sub_le_sub_right hhi 1
  have hg : fiberBandGrowthOrder m 64 ≤ 2625 := by
    simp only [fiberBandGrowthOrder, ite_eq_right (by norm_num only : 64 ≠ 20)]
    nlinarith only [hm1]
  have hg2 := Nat.pow_le_pow_left hg 2
  have hprod := Nat.mul_le_mul hg2 hm1
  have he : (fiberBandGrowthOrder m 64) ^ 2 * (m - 1) ≤ 282515625 := by
    calc
      _ ≤ 2625 ^ 2 * 41 := hprod
      _ ≤ 282515625 := by norm_num only
  have hr : fiberBandMomentOrder m 64 ≤ 72324000001 := by
    simp only [fiberBandMomentOrder, ite_eq_right (by norm_num only : 64 ≠ 20)]
    calc
      _ ≤ 4 * 64 * 2625 ^ 2 * 41 + 1 := by
        apply Nat.add_le_add_right
        exact Nat.mul_le_mul (Nat.mul_le_mul_left (4 * 64) hg2) hm1
      _ ≤ 72324000001 := by norm_num only
  have h2r : 2 * fiberBandMomentOrder m 64 < 2 ^ 38 := by
    calc
      _ ≤ 2 * 72324000001 := Nat.mul_le_mul_left 2 hr
      _ < 2 ^ 38 := by norm_num only
  have hlog2r : Nat.log2 (2 * fiberBandMomentOrder m 64) < 38 := by
    rw [Nat.log2_eq_log_two]
    exact
      Nat.log_lt_of_lt_pow (Nat.ne_of_gt (Nat.mul_pos (by decide) (fiberBandMomentOrder_pos m 64)))
        h2r
  have hlog2r' : Nat.log2 (2 * fiberBandMomentOrder m 64) + 1 ≤ 38 := Nat.succ_le_iff.mpr hlog2r
  have hmul := Nat.mul_le_mul_left (2 * fiberBandMomentOrder m 64) hlog2r'
  have hP :
    2 * fiberBandMomentOrder m 64 * (Nat.log2 (2 * fiberBandMomentOrder m 64) + 1) +
        2 * fiberBandMomentOrder m 64 <
      2 ^ 44 := by
    calc
      _ ≤ 2 * fiberBandMomentOrder m 64 * 38 + 2 * fiberBandMomentOrder m 64 :=
        Nat.add_le_add_right hmul _
      _ ≤ 78 * 72324000001 := by nlinarith only [hr]
      _ < 2 ^ 44 := by norm_num only
  have hPpos :
    0 <
      2 * fiberBandMomentOrder m 64 * (Nat.log2 (2 * fiberBandMomentOrder m 64) + 1) +
        2 * fiberBandMomentOrder m 64 := by
    have hterm : 0 < 2 * fiberBandMomentOrder m 64 :=
      Nat.mul_pos (by decide) (fiberBandMomentOrder_pos m 64)
    have hnonneg :
      0 ≤ 2 * fiberBandMomentOrder m 64 * (Nat.log2 (2 * fiberBandMomentOrder m 64) + 1) :=
      Nat.zero_le _
    nlinarith only [hterm, hnonneg]
  have hlogP' :
    Nat.log2
        (2 * fiberBandMomentOrder m 64 * (Nat.log2 (2 * fiberBandMomentOrder m 64) + 1) +
          2 * fiberBandMomentOrder m 64) <
      44 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hPpos) hP
  have hlogP :
    Nat.log2
          (2 * fiberBandMomentOrder m 64 * (Nat.log2 (2 * fiberBandMomentOrder m 64) + 1) +
            2 * fiberBandMomentOrder m 64) +
        1 ≤
      44 :=
    Nat.succ_le_iff.mpr hlogP'
  nlinarith only [hr, he, hlogP]

/-- Each degree 2≤m≤42 at precision 64 has coefficient at most
2^(2^145000000000). Apply the logarithmic quotient estimate. -/
theorem fiberBandCoefficient_64_le_double_exp {m : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42) :
    fiberBandCoefficient m 64 ≤ 2 ^ (2 ^ 145000000000) := by
  have hgpos : 1 ≤ fiberBandGrowthOrder m 64 := Nat.succ_le_iff.mpr (fiberBandGrowthOrder_pos m 64)
  have hm1 : 1 ≤ m - 1 := Nat.sub_le_sub_right hlo 1
  have hprod : 1 ≤ fiberBandGrowthOrder m 64 ^ 2 * (m - 1) :=
    Nat.mul_le_mul (Nat.one_le_pow _ _ hgpos) hm1
  have hrlo : 4 ≤ fiberBandMomentOrder m 64 := by
    have hprod' : 1 ≤ (64 * (m - 1) + 1) ^ 2 * (m - 1) := by
      simpa only [fiberBandGrowthOrder, ite_eq_right (by norm_num only : 64 ≠ 20)] using hprod
    simp only [fiberBandMomentOrder, fiberBandGrowthOrder,
      ite_eq_right (by norm_num only : 64 ≠ 20)]
    nlinarith only [hprod']
  apply fiberBandCoefficient_le_double_exp_of_log_order_budget hrlo
  exact fiberBand_orders_64_improved_budget hhi

/-- The full count coefficient at a=32,c=64 is below
2^(2^(145000000000+1)). Combine the degree sum and harmonic factor first. -/
theorem finiteFiberCountCoefficient_64_32_lt_double_exp :
    finiteFiberCountCoefficient 64 32 < 2 ^ (2 ^ (145000000000 + 1)) := by
  apply finiteFiberCountCoefficient_lt_double_exp_of_degree_bounds
  · calc
      36 * (2 * 32 + 1) = 2340 := by norm_num only
      _ < 5796 := by norm_num only
      _ < 2 ^ (2 ^ 145000000000) :=
        finiteFiberCount_harmonic_factor_lt_unit (B := 145000000000)
          (by norm_num only : (4 : ℕ) ≤ 145000000000)
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h | h | h | h | h | h
    all_goals subst m; exact fiberBandCoefficient_64_le_double_exp (by decide) (by decide)

/-- For degrees m≤42 at precision 20, the logarithmic quotient budget is
below 76,596,732. Degree 42 uses its exact quotient moment order; lower
degrees use the uniform bound 16n²+1. -/
theorem fiberBand_orders_20_improved_budget {m : ℕ} (hhi : m ≤ 42) :
    2 * fiberBandMomentOrder m 20 +
        Nat.log2
          (2 * fiberBandMomentOrder m 20 * (Nat.log2 (2 * fiberBandMomentOrder m 20) + 1) +
            2 * fiberBandMomentOrder m 20) +
        (fiberBandGrowthOrder m 20) ^ 2 * (m - 1) +
        4 ≤
      76596732 := by
  by_cases h42 : m = 42
  · subst m
    decide
  · have hm41 : m ≤ 41 := by omega
    have hm1 : m - 1 ≤ 40 := Nat.sub_le_sub_right hm41 1
    let g := 20 * (m - 1)
    let s := max 1 ((266 * g + 999) / 1000)
    have hs : 0 < s := by
      dsimp only [s]; omega
    have hg4 : g ≤ 4 * s := by
      dsimp only [g, s]; omega
    have hgs : g + s ≤ 1016 := by
      dsimp only [g, s]; omega
    have hfour : 4 * g ≤ 16 * s := by nlinarith only [hg4]
    have hmul := Nat.mul_le_mul_right ((g + s) ^ 2) hfour
    have hdiv : (4 * g * (g + s) ^ 2) / s ≤ 16 * (g + s) ^ 2 := by
      apply Nat.div_le_of_le_mul
      calc
        4 * g * (g + s) ^ 2 ≤ 16 * s * (g + s) ^ 2 := hmul
        _ = s * (16 * (g + s) ^ 2) := by ring
    have hr : fiberBandMomentOrder m 20 ≤ 16516097 := by
      change (4 * g * (g + s) ^ 2) / s + 1 ≤ 16516097
      calc
        _ ≤ 16 * (g + s) ^ 2 + 1 := Nat.add_le_add_right hdiv 1
        _ ≤ 16516097 := by nlinarith only [hgs]
    have hgs' : fiberBandGrowthOrder m 20 ≤ 1016 := by
      change 20 * (m - 1) + max 1 ((266 * (20 * (m - 1)) + 999) / 1000) ≤ 1016
      dsimp only [g, s] at hgs
      exact hgs
    have hnsq : (fiberBandGrowthOrder m 20) ^ 2 ≤ 1016 ^ 2 := Nat.pow_le_pow_left hgs' 2
    have he : (fiberBandGrowthOrder m 20) ^ 2 * (m - 1) ≤ 1016 ^ 2 * 40 := Nat.mul_le_mul hnsq hm1
    have h2r : 2 * fiberBandMomentOrder m 20 < 2 ^ 25 := by
      calc
        _ ≤ 2 * 16516097 := Nat.mul_le_mul_left 2 hr
        _ < 2 ^ 25 := by norm_num only
    have hlog2r : Nat.log2 (2 * fiberBandMomentOrder m 20) < 25 := by
      rw [Nat.log2_eq_log_two]
      exact
        Nat.log_lt_of_lt_pow
          (Nat.ne_of_gt (Nat.mul_pos (by decide) (fiberBandMomentOrder_pos m 20))) h2r
    have hlog2r' : Nat.log2 (2 * fiberBandMomentOrder m 20) + 1 ≤ 25 := Nat.succ_le_iff.mpr hlog2r
    have hmul' := Nat.mul_le_mul_left (2 * fiberBandMomentOrder m 20) hlog2r'
    have hP :
      2 * fiberBandMomentOrder m 20 * (Nat.log2 (2 * fiberBandMomentOrder m 20) + 1) +
          2 * fiberBandMomentOrder m 20 <
        2 ^ 30 := by
      calc
        _ ≤ 2 * fiberBandMomentOrder m 20 * 25 + 2 * fiberBandMomentOrder m 20 :=
          Nat.add_le_add_right hmul' _
        _ = 52 * fiberBandMomentOrder m 20 := by ring
        _ ≤ 52 * 16516097 := Nat.mul_le_mul_left 52 hr
        _ < 2 ^ 30 := by norm_num only
    have hPpos :
      0 <
        2 * fiberBandMomentOrder m 20 * (Nat.log2 (2 * fiberBandMomentOrder m 20) + 1) +
          2 * fiberBandMomentOrder m 20 := by
      have hterm : 0 < 2 * fiberBandMomentOrder m 20 :=
        Nat.mul_pos (by decide) (fiberBandMomentOrder_pos m 20)
      have hnonneg :
        0 ≤ 2 * fiberBandMomentOrder m 20 * (Nat.log2 (2 * fiberBandMomentOrder m 20) + 1) :=
        Nat.zero_le _
      nlinarith only [hterm, hnonneg]
    have hlogP :
      Nat.log2
          (2 * fiberBandMomentOrder m 20 * (Nat.log2 (2 * fiberBandMomentOrder m 20) + 1) +
            2 * fiberBandMomentOrder m 20) ≤
        29 := by
      have hlogP' :
        Nat.log2
            (2 * fiberBandMomentOrder m 20 * (Nat.log2 (2 * fiberBandMomentOrder m 20) + 1) +
              2 * fiberBandMomentOrder m 20) <
          30 := by
        rw [Nat.log2_eq_log_two]
        exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hPpos) hP
      omega
    omega

/-- The quarter-range prime count saves one unit from the precision-20
coefficient budget. Subtract one from the positive moment contribution. -/
theorem fiberBand_orders_20_quarter_budget {m : ℕ} (hhi : m ≤ 42) :
    2 * fiberBandMomentOrder m 20 - 1 +
        Nat.log2
          (2 * fiberBandMomentOrder m 20 * (Nat.log2 (2 * fiberBandMomentOrder m 20) + 1) +
            2 * fiberBandMomentOrder m 20) +
        (fiberBandGrowthOrder m 20) ^ 2 * (m - 1) +
        4 ≤
      76596731 := by
  have hbudget := fiberBand_orders_20_improved_budget hhi
  have hr : 1 ≤ fiberBandMomentOrder m 20 := by
    exact Nat.succ_le_iff.mpr (fiberBandMomentOrder_pos m 20)
  omega

/-- Every degree 2≤m≤42 at precision 20 has coefficient at most
2^(2^76,596,731). Apply the logarithmic quotient estimate. -/
theorem fiberBandCoefficient_20_le_double_exp {m : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42) :
    fiberBandCoefficient m 20 ≤ 2 ^ (2 ^ 76596731) := by
  have hgpos : 1 ≤ fiberBandGrowthOrder m 20 := Nat.succ_le_iff.mpr (fiberBandGrowthOrder_pos m 20)
  have hm1 : 1 ≤ m - 1 := Nat.sub_le_sub_right hlo 1
  have hprod : 1 ≤ fiberBandGrowthOrder m 20 ^ 2 * (m - 1) :=
    Nat.mul_le_mul (Nat.one_le_pow _ _ hgpos) hm1
  have hrlo : 7 ≤ fiberBandMomentOrder m 20 := by
    let g := 20 * (m - 1)
    let s := max 1 ((266 * g + 999) / 1000)
    have hg20 : 20 ≤ g := by
      dsimp only [g]; omega
    have hs : 0 < s := by
      dsimp only [s]; omega
    have hsle : s ≤ g := by
      dsimp only [s, g]; omega
    have hgs : g ≤ g + s := Nat.le_add_right g s
    have hgs2 := Nat.pow_le_pow_left hgs 2
    have h6 : 6 ≤ 4 * g ^ 2 := by nlinarith only [hg20]
    have h6g := Nat.mul_le_mul_right g h6
    have hlow : 6 * s ≤ 4 * g * (g + s) ^ 2 := by
      calc
        6 * s ≤ 6 * g := Nat.mul_le_mul_left 6 hsle
        _ ≤ 4 * g ^ 2 * g := by nlinarith only [h6g]
        _ = 4 * g * g ^ 2 := by ring
        _ ≤ 4 * g * (g + s) ^ 2 := Nat.mul_le_mul_left (4 * g) hgs2
    have hq : 6 ≤ (4 * g * (g + s) ^ 2) / s :=
      (Nat.le_div_iff_mul_le hs).2 (by nlinarith only [hlow])
    change (4 * g * (g + s) ^ 2) / s + 1 ≥ 7
    omega
  apply fiberBandCoefficient_le_double_exp_of_log_order_budget_quarter hrlo
  exact fiberBand_orders_20_quarter_budget hhi

/-- The full count coefficient at a=10,c=20 is below
2^(2^(76,596,732)). Combine the degree sum and harmonic factor. -/
theorem finiteFiberCountCoefficient_20_10_lt_double_exp :
    finiteFiberCountCoefficient 20 10 < 2 ^ (2 ^ (76596731 + 1)) := by
  apply finiteFiberCountCoefficient_lt_double_exp_of_degree_bounds
  · calc
      36 * (2 * 10 + 1) = 756 := by norm_num only
      _ < 5796 := by norm_num only
      _ < 2 ^ (2 ^ 76596731) :=
        finiteFiberCount_harmonic_factor_lt_unit (B := 76596731)
          (by norm_num only : (4 : ℕ) ≤ 76596731)
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h | h | h | h | h | h
    all_goals subst m; exact fiberBandCoefficient_20_le_double_exp (by decide) (by decide)

end PseudoPrime.NumberTheory.Heilbronn
