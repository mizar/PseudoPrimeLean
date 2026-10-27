/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.DoubleExponentialBudgets
public import PseudoPrime.NumberTheory.Heilbronn.ExplicitFiberEnergyThreshold
public import PseudoPrime.NumberTheory.Heilbronn.ExplicitFiberCoefficientBudget
public import PseudoPrime.NumberTheory.Heilbronn.EightDegreeRatioBounds
public import PseudoPrime.NumberTheory.Heilbronn.FiberBandCoefficients
public import PseudoPrime.NumberTheory.Heilbronn.HeightWeightExchange
public import PseudoPrime.NumberTheory.Heilbronn.RationalFiberRatioBands

/-! # Alternative finite-fiber orders with a free height-loss parameter -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Binary length bound for the exponent in a double-exponential coefficient.
Input: `Q ≤ 2^(2^B)` and a natural exponent `e`. Claim: `Q^e` fits with only
`Nat.log2 e + 1` additional inner bits. The standard upper bound on `e` by
its next power of two supplies the exponent budget without evaluating towers. -/
theorem pow_le_double_exp_add_of_log2 {Q B e : ℕ} (hQ : Q ≤ 2 ^ (2 ^ B)) :
    Q ^ e ≤ 2 ^ (2 ^ (B + Nat.log2 e + 1)) := by
  exact
    pow_le_double_exp_add_of_exponent_bound hQ (e := e) (ell := Nat.log2 e + 1)
      (Nat.lt_log2_self (n := e)).le

/-- Growth order for degree `m` and precision `c` in the free-order family.
Set `G = c(m - 1)` and choose `n = 2G + 1`; unlike
`fiberBandGrowthOrder`, this alternative does not optimize the moment order
separately. It retains the exact algebraic margin used below. -/
def fiberBandFreeGrowthOrder (m c : ℕ) : ℕ :=
  2 * (c * (m - 1)) + 1

/-- Moment order paired with `fiberBandFreeGrowthOrder`. For `G = c(m - 1)`,
the choice `r = 16G² + 4` makes `n r - G r - 4G n² = 4`. -/
def fiberBandFreeMomentOrder (m c : ℕ) : ℕ :=
  16 * (c * (m - 1)) ^ 2 + 4

/-- The explicit band coefficient for the free-order family, with the same
quotient constant and fivefold band aggregation as the existing family. -/
def fiberBandFreeCoefficient (m c : ℕ) : ℕ :=
  5 *
      (quotientPowerBoundConstant (fiberBandFreeMomentOrder m c) ^
          (fiberBandFreeGrowthOrder m c ^ 2 * (m - 1)) +
        1) +
    1

/-- The free growth order is positive for all degrees and precisions. -/
theorem fiberBandFreeGrowthOrder_pos (m c : ℕ) : 0 < fiberBandFreeGrowthOrder m c := by
  exact Nat.succ_pos _

/-- The free moment order is positive because it has an additive constant four. -/
theorem fiberBandFreeMomentOrder_pos (m c : ℕ) : 0 < fiberBandFreeMomentOrder m c := by
  exact Nat.lt_of_lt_of_le (by decide : 0 < 4) (Nat.le_add_left _ _)

/-- For positive degree `m`, the free orders leave an exact positive height gap.
After setting `G = c(m - 1)`, expand `n r = G r + 4G n² + 4` and multiply
the strict four-unit margin by `m`. -/
theorem fiberBandFree_parameters_small_loss {m c : ℕ} (hm : 0 < m) :
    c * heightRatioLossExponent m (fiberBandFreeGrowthOrder m c) (fiberBandFreeMomentOrder m c) <
      fiberBandFreeGrowthOrder m c * m * fiberBandFreeMomentOrder m c := by
  let G : ℕ := c * (m - 1)
  let n : ℕ := 2 * G + 1
  let r : ℕ := 16 * G ^ 2 + 4
  have hid : n * r = G * r + 4 * G * n ^ 2 + 4 := by
    dsimp only [n, r]
    ring
  change c * heightRatioLossExponent m n r < n * m * r
  rw [heightRatioLossExponent]
  have hmain : c * ((m - 1) * m * r + 4 * m * (n ^ 2 * (m - 1))) = m * (G * r + 4 * G * n ^ 2) := by
    dsimp only [G]
    ring
  rw [hmain]
  calc
    m * (G * r + 4 * G * n ^ 2) < m * (n * r) := by
      rw [hid]
      exact Nat.mul_lt_mul_of_pos_left (Nat.lt_add_of_pos_right (by decide : 0 < 4)) hm
    _ = n * m * r := by ring

/-- If the logarithmic quotient budget and the binary length of the free
growth exponent fit `B`, the alternative degree coefficient is at most
`2^(2^B)`. Use the quarter-range quotient estimate and absorb the natural
power exponent by its binary length. -/
theorem fiberBandFreeCoefficient_le_double_exp_of_quarter_budget {m c B : ℕ}
    (hr : 7 ≤ fiberBandFreeMomentOrder m c)
    (hbudget :
      2 * fiberBandFreeMomentOrder m c - 1 +
          Nat.log2
            (2 * fiberBandFreeMomentOrder m c * (Nat.log2 (2 * fiberBandFreeMomentOrder m c) + 1) +
              2 * fiberBandFreeMomentOrder m c) +
          Nat.log2 (fiberBandFreeGrowthOrder m c ^ 2 * (m - 1)) +
          1 +
          4 ≤
        B) :
    fiberBandFreeCoefficient m c ≤ 2 ^ (2 ^ B) := by
  have hQ := quotientPowerBoundConstant_le_double_exp_log_quarter hr
  have hD := pow_le_double_exp_add_of_log2 (e := fiberBandFreeGrowthOrder m c ^ 2 * (m - 1)) hQ
  have hC := band_coefficient_le_double_exp hD
  have hbudget' :
    (2 * fiberBandFreeMomentOrder m c - 1 +
          Nat.log2
            (2 * fiberBandFreeMomentOrder m c * (Nat.log2 (2 * fiberBandFreeMomentOrder m c) + 1) +
              2 * fiberBandFreeMomentOrder m c) +
          Nat.log2 (fiberBandFreeGrowthOrder m c ^ 2 * (m - 1)) +
          1) +
        4 ≤
      B := by
    nlinarith only [hbudget]
  exact
    hC.trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.pow_le_pow_right (by decide : 0 < 2) hbudget'))

/-- If `D` is at least two, the band multiplier fits eight copies of its
quotient coefficient. This saves one inner exponent bit over the uniform
bound when specializing the free-order coefficients. -/
theorem band_coefficient_le_double_exp_three {D B : ℕ} (hD : D ≤ 2 ^ (2 ^ B)) (hDtwo : 2 ≤ D) :
    5 * (D + 1) + 1 ≤ 2 ^ (2 ^ (B + 3)) := by
  have hlinear : 5 * (D + 1) + 1 ≤ 8 * D := by nlinarith only [hDtwo]
  have hmul : 8 * D ≤ 8 * 2 ^ (2 ^ B) := Nat.mul_le_mul_left 8 hD
  have hscale := mul_le_double_exp_add (A := 8) (B := B) (k := 3) (by decide)
  exact hlinear.trans (hmul.trans hscale)

/-- The quotient coefficient is at least two for moment orders in the free
family. Its factor `8^r` alone supplies this lower bound. -/
theorem quotientPowerBoundConstant_two_le_of_seven_le {r : ℕ} (hr : 7 ≤ r) :
    2 ≤ quotientPowerBoundConstant r := by
  have hrone : 1 ≤ r := Nat.le_trans (by decide) hr
  have hpow : 2 ≤ 8 ^ r := by
    calc
      2 ≤ 8 := by norm_num only
      _ ≤ 8 ^ r := Nat.pow_le_pow_right (by decide : 0 < 8) hrone
  have hfactor : 1 ≤ 9 * r.factorial := by
    have hf := Nat.factorial_pos r
    nlinarith only [hf]
  have hdivisor : 1 ≤ divisorPowerBoundConstant (2 * r) := by
    unfold divisorPowerBoundConstant
    exact Nat.one_le_pow _ _ (Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos (by decide : 0 < 2)))
  unfold quotientPowerBoundConstant
  calc
    2 ≤ 8 ^ r := hpow
    _ = (8 ^ r * 1) * 1 := by simp only [Nat.mul_one]
    _ ≤ (8 ^ r * (9 * r.factorial)) * divisorPowerBoundConstant (2 * r) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hfactor) hdivisor

/-- Use the sharper band coefficient bound when the quotient-growth constant
is at least two. This saves one bit in the inner exponent budget. -/
theorem fiberBandFreeCoefficient_le_double_exp_of_quarter_budget_three {m c B : ℕ}
    (hr : 7 ≤ fiberBandFreeMomentOrder m c) (hepos : 0 < fiberBandFreeGrowthOrder m c ^ 2 * (m - 1))
    (hbudget :
      2 * fiberBandFreeMomentOrder m c - 1 +
          Nat.log2
            (2 * fiberBandFreeMomentOrder m c * (Nat.log2 (2 * fiberBandFreeMomentOrder m c) + 1) +
              2 * fiberBandFreeMomentOrder m c) +
          Nat.log2 (fiberBandFreeGrowthOrder m c ^ 2 * (m - 1)) +
          1 +
          3 ≤
        B) :
    fiberBandFreeCoefficient m c ≤ 2 ^ (2 ^ B) := by
  have hQ := quotientPowerBoundConstant_le_double_exp_log_quarter hr
  have hQtwo := quotientPowerBoundConstant_two_le_of_seven_le hr
  have h2pow : 2 ≤ 2 ^ (fiberBandFreeGrowthOrder m c ^ 2 * (m - 1)) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_iff.mpr hepos)
  have hDtwo :
    2 ≤
      quotientPowerBoundConstant (fiberBandFreeMomentOrder m c) ^
        (fiberBandFreeGrowthOrder m c ^ 2 * (m - 1)) :=
    h2pow.trans (Nat.pow_le_pow_left hQtwo _)
  have hD := pow_le_double_exp_add_of_log2 (e := fiberBandFreeGrowthOrder m c ^ 2 * (m - 1)) hQ
  have hC := band_coefficient_le_double_exp_three hD hDtwo
  have hbudget' :
    (2 * fiberBandFreeMomentOrder m c - 1 +
          Nat.log2
            (2 * fiberBandFreeMomentOrder m c * (Nat.log2 (2 * fiberBandFreeMomentOrder m c) + 1) +
              2 * fiberBandFreeMomentOrder m c) +
          Nat.log2 (fiberBandFreeGrowthOrder m c ^ 2 * (m - 1)) +
          1) +
        3 ≤
      B := by
    nlinarith only [hbudget]
  exact
    hC.trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.pow_le_pow_right (by decide : 0 < 2) hbudget'))

/-- For every degree `2 ≤ m ≤ 42`, the free-order coefficient at `c=20`
fits the common budget `2^(2^21516867)`. Bound the moment order by its
endpoint value and use binary lengths 25, 30, and 27 for the quotient and
growth factors. The proof keeps all factorial and tower values symbolic. -/
theorem fiberBandFree_orders_20_budget {m : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42) :
    2 * fiberBandFreeMomentOrder m 20 - 1 +
        Nat.log2
          (2 * fiberBandFreeMomentOrder m 20 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 20) + 1) +
            2 * fiberBandFreeMomentOrder m 20) +
        Nat.log2 (fiberBandFreeGrowthOrder m 20 ^ 2 * (m - 1)) +
        1 +
        4 ≤
      21516867 := by
  have hm1 : m - 1 ≤ 41 := Nat.sub_le_sub_right hhi 1
  have hmlow : 1 ≤ m - 1 := by
    have h := Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans hlo)
    nlinarith only [h, hlo]
  have hG : 20 * (m - 1) ≤ 820 := by
    calc
      _ ≤ 20 * 41 := Nat.mul_le_mul_left 20 hm1
      _ = 820 := by norm_num only
  have hn : fiberBandFreeGrowthOrder m 20 ≤ 1641 := by
    simp only [fiberBandFreeGrowthOrder]
    nlinarith only [hG]
  have hr : fiberBandFreeMomentOrder m 20 ≤ 10758404 := by
    simp only [fiberBandFreeMomentOrder]
    nlinarith only [hG]
  have hE : fiberBandFreeGrowthOrder m 20 ^ 2 * (m - 1) ≤ 110408121 := by
    calc
      _ ≤ 1641 ^ 2 * 41 := Nat.mul_le_mul (Nat.pow_le_pow_left hn 2) hm1
      _ = 110408121 := by norm_num only
  have h2r : 2 * fiberBandFreeMomentOrder m 20 < 2 ^ 25 := by
    calc
      _ ≤ 2 * 10758404 := Nat.mul_le_mul_left 2 hr
      _ < 2 ^ 25 := by norm_num only
  have hrpos : 0 < fiberBandFreeMomentOrder m 20 := fiberBandFreeMomentOrder_pos m 20
  have h2rpos : 0 < 2 * fiberBandFreeMomentOrder m 20 := Nat.mul_pos (by decide) hrpos
  have hlog2r : Nat.log2 (2 * fiberBandFreeMomentOrder m 20) < 25 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt h2rpos) h2r
  have hlog2r' : Nat.log2 (2 * fiberBandFreeMomentOrder m 20) + 1 ≤ 25 := Nat.succ_le_iff.mpr hlog2r
  have hP :
    2 * fiberBandFreeMomentOrder m 20 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 20) + 1) +
        2 * fiberBandFreeMomentOrder m 20 <
      2 ^ 30 := by
    calc
      _ ≤ 2 * fiberBandFreeMomentOrder m 20 * 25 + 2 * fiberBandFreeMomentOrder m 20 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hlog2r') _
      _ ≤ 52 * 10758404 := by nlinarith only [hr]
      _ < 2 ^ 30 := by norm_num only
  have hPpos :
    0 <
      2 * fiberBandFreeMomentOrder m 20 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 20) + 1) +
        2 * fiberBandFreeMomentOrder m 20 :=
    lt_of_lt_of_le h2rpos (Nat.le_add_left _ _)
  have hlogP :
    Nat.log2
        (2 * fiberBandFreeMomentOrder m 20 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 20) + 1) +
          2 * fiberBandFreeMomentOrder m 20) <
      30 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hPpos) hP
  have hlogP' :
    Nat.log2
          (2 * fiberBandFreeMomentOrder m 20 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 20) + 1) +
            2 * fiberBandFreeMomentOrder m 20) +
        1 ≤
      30 :=
    Nat.succ_le_iff.mpr hlogP
  have hEpos : 0 < fiberBandFreeGrowthOrder m 20 ^ 2 * (m - 1) :=
    Nat.mul_pos (Nat.pow_pos (fiberBandFreeGrowthOrder_pos m 20))
      (lt_of_lt_of_le (by decide : 0 < 1) hmlow)
  have hEpow : fiberBandFreeGrowthOrder m 20 ^ 2 * (m - 1) < 2 ^ 27 := by
    calc
      _ ≤ 110408121 := hE
      _ < 2 ^ 27 := by norm_num only
  have hlogE : Nat.log2 (fiberBandFreeGrowthOrder m 20 ^ 2 * (m - 1)) < 27 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hEpos) hEpow
  have hlogE' : Nat.log2 (fiberBandFreeGrowthOrder m 20 ^ 2 * (m - 1)) + 1 ≤ 27 :=
    Nat.succ_le_iff.mpr hlogE
  have hfirst : 2 * fiberBandFreeMomentOrder m 20 - 1 ≤ 21516807 := by
    have h := Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hr) 1
    nlinarith only [h]
  nlinarith only [hfirst, hlogP', hlogE']

/-- Every degree `2 ≤ m ≤ 42` at precision 20 has free-order coefficient
at most `2^(2^21516867)`. Apply the shared quarter-range magnitude estimate. -/
theorem fiberBandFreeCoefficient_20_le_double_exp {m B : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42)
    (hB : 21516867 ≤ B) : fiberBandFreeCoefficient m 20 ≤ 2 ^ (2 ^ B) := by
  have hGlo : 20 ≤ 20 * (m - 1) := by
    have hmlow : 1 ≤ m - 1 := by
      have h := Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans hlo)
      nlinarith only [h, hlo]
    exact Nat.mul_le_mul_left 20 hmlow
  have hr : 7 ≤ fiberBandFreeMomentOrder m 20 := by
    simp only [fiberBandFreeMomentOrder]
    nlinarith only [hGlo]
  have hbudget := fiberBandFree_orders_20_budget hlo hhi
  exact fiberBandFreeCoefficient_le_double_exp_of_quarter_budget hr (hbudget.trans hB)

/-- For degrees from 2 through 42, precision 162 gives a common inner
double-exponential budget of 1411717327. Bound the order parameters at degree
42 and retain symbolic binary logarithms for the quotient estimates. -/
theorem fiberBandFree_orders_162_budget {m : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42) :
    2 * fiberBandFreeMomentOrder m 162 - 1 +
        Nat.log2
          (2 * fiberBandFreeMomentOrder m 162 *
              (Nat.log2 (2 * fiberBandFreeMomentOrder m 162) + 1) +
            2 * fiberBandFreeMomentOrder m 162) +
        Nat.log2 (fiberBandFreeGrowthOrder m 162 ^ 2 * (m - 1)) +
        1 +
        3 ≤
      1411717327 := by
  have hm1 : m - 1 ≤ 41 := Nat.sub_le_sub_right hhi 1
  have hmlow : 1 ≤ m - 1 := by
    have h := Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans hlo)
    nlinarith only [h, hlo]
  have hG : 162 * (m - 1) ≤ 6642 := by
    calc
      _ ≤ 162 * 41 := Nat.mul_le_mul_left 162 hm1
      _ = 6642 := by norm_num only
  have hn : fiberBandFreeGrowthOrder m 162 ≤ 13285 := by
    simp only [fiberBandFreeGrowthOrder]
    nlinarith only [hG]
  have hr : fiberBandFreeMomentOrder m 162 ≤ 705858628 := by
    simp only [fiberBandFreeMomentOrder]
    nlinarith only [hG]
  have hE : fiberBandFreeGrowthOrder m 162 ^ 2 * (m - 1) ≤ 7236140225 := by
    calc
      _ ≤ 13285 ^ 2 * 41 := Nat.mul_le_mul (Nat.pow_le_pow_left hn 2) hm1
      _ = 7236140225 := by norm_num only
  have h2r : 2 * fiberBandFreeMomentOrder m 162 < 2 ^ 31 := by
    calc
      _ ≤ 2 * 705858628 := Nat.mul_le_mul_left 2 hr
      _ < 2 ^ 31 := by norm_num only
  have hrpos : 0 < fiberBandFreeMomentOrder m 162 := fiberBandFreeMomentOrder_pos m 162
  have h2rpos : 0 < 2 * fiberBandFreeMomentOrder m 162 := Nat.mul_pos (by decide) hrpos
  have hlog2r : Nat.log2 (2 * fiberBandFreeMomentOrder m 162) < 31 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt h2rpos) h2r
  have hlog2r' : Nat.log2 (2 * fiberBandFreeMomentOrder m 162) + 1 ≤ 31 :=
    Nat.succ_le_iff.mpr hlog2r
  have hP :
    2 * fiberBandFreeMomentOrder m 162 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 162) + 1) +
        2 * fiberBandFreeMomentOrder m 162 <
      2 ^ 36 := by
    calc
      _ ≤ 2 * fiberBandFreeMomentOrder m 162 * 31 + 2 * fiberBandFreeMomentOrder m 162 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hlog2r') _
      _ ≤ 64 * 705858628 := by nlinarith only [hr]
      _ < 2 ^ 36 := by norm_num only
  have hPpos :
    0 <
      2 * fiberBandFreeMomentOrder m 162 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 162) + 1) +
        2 * fiberBandFreeMomentOrder m 162 :=
    lt_of_lt_of_le h2rpos (Nat.le_add_left _ _)
  have hlogP :
    Nat.log2
        (2 * fiberBandFreeMomentOrder m 162 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 162) + 1) +
          2 * fiberBandFreeMomentOrder m 162) <
      36 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hPpos) hP
  have hlogPLe :
    Nat.log2
        (2 * fiberBandFreeMomentOrder m 162 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 162) + 1) +
          2 * fiberBandFreeMomentOrder m 162) ≤
      35 :=
    Nat.le_of_lt_succ hlogP
  have hEpos : 0 < fiberBandFreeGrowthOrder m 162 ^ 2 * (m - 1) :=
    Nat.mul_pos (Nat.pow_pos (fiberBandFreeGrowthOrder_pos m 162)) hmlow
  have hEpow : fiberBandFreeGrowthOrder m 162 ^ 2 * (m - 1) < 2 ^ 33 := by
    calc
      _ ≤ 7236140225 := hE
      _ < 2 ^ 33 := by norm_num only
  have hlogE : Nat.log2 (fiberBandFreeGrowthOrder m 162 ^ 2 * (m - 1)) < 33 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hEpos) hEpow
  have hlogE' : Nat.log2 (fiberBandFreeGrowthOrder m 162 ^ 2 * (m - 1)) + 1 ≤ 33 :=
    Nat.succ_le_iff.mpr hlogE
  have hfirst : 2 * fiberBandFreeMomentOrder m 162 - 1 ≤ 1411717255 := by
    have h := Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hr) 1
    nlinarith only [h]
  nlinarith only [hfirst, hlogPLe, hlogE']

/-- For degrees with 2 ≤ m ≤ 42, free precision 168 fits the common inner
double-exponential coefficient budget 1,518,225,486. Bound the moment and
growth orders at degree 42 and estimate their binary logarithms explicitly. -/
theorem fiberBandFree_orders_168_budget {m : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42) :
    2 * fiberBandFreeMomentOrder m 168 - 1 +
        Nat.log2
          (2 * fiberBandFreeMomentOrder m 168 *
              (Nat.log2 (2 * fiberBandFreeMomentOrder m 168) + 1) +
            2 * fiberBandFreeMomentOrder m 168) +
        Nat.log2 (fiberBandFreeGrowthOrder m 168 ^ 2 * (m - 1)) +
        1 +
        3 ≤
      1518225486 := by
  have hm1 : m - 1 ≤ 41 := Nat.sub_le_sub_right hhi 1
  have hmlow : 1 ≤ m - 1 := by
    have h := Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans hlo)
    nlinarith only [h, hlo]
  have hG : 168 * (m - 1) ≤ 6888 := by
    calc
      _ ≤ 168 * 41 := Nat.mul_le_mul_left 168 hm1
      _ = 6888 := by norm_num only
  have hn : fiberBandFreeGrowthOrder m 168 ≤ 13777 := by
    simp only [fiberBandFreeGrowthOrder]
    nlinarith only [hG]
  have hr : fiberBandFreeMomentOrder m 168 ≤ 759112708 := by
    simp only [fiberBandFreeMomentOrder]
    nlinarith only [hG]
  have hE : fiberBandFreeGrowthOrder m 168 ^ 2 * (m - 1) ≤ 7782034889 := by
    calc
      _ ≤ 13777 ^ 2 * 41 := Nat.mul_le_mul (Nat.pow_le_pow_left hn 2) hm1
      _ = 7782034889 := by norm_num only
  have h2r : 2 * fiberBandFreeMomentOrder m 168 < 2 ^ 31 := by
    calc
      _ ≤ 2 * 759112708 := Nat.mul_le_mul_left 2 hr
      _ < 2 ^ 31 := by norm_num only
  have hrpos : 0 < fiberBandFreeMomentOrder m 168 := fiberBandFreeMomentOrder_pos m 168
  have h2rpos : 0 < 2 * fiberBandFreeMomentOrder m 168 := Nat.mul_pos (by decide) hrpos
  have hlog2r : Nat.log2 (2 * fiberBandFreeMomentOrder m 168) < 31 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt h2rpos) h2r
  have hlog2r' : Nat.log2 (2 * fiberBandFreeMomentOrder m 168) + 1 ≤ 31 :=
    Nat.succ_le_iff.mpr hlog2r
  have hP :
    2 * fiberBandFreeMomentOrder m 168 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 168) + 1) +
        2 * fiberBandFreeMomentOrder m 168 <
      2 ^ 36 := by
    calc
      _ ≤ 2 * fiberBandFreeMomentOrder m 168 * 31 + 2 * fiberBandFreeMomentOrder m 168 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hlog2r') _
      _ ≤ 64 * 759112708 := by nlinarith only [hr]
      _ < 2 ^ 36 := by norm_num only
  have hPpos :
    0 <
      2 * fiberBandFreeMomentOrder m 168 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 168) + 1) +
        2 * fiberBandFreeMomentOrder m 168 :=
    lt_of_lt_of_le h2rpos (Nat.le_add_left _ _)
  have hlogP :
    Nat.log2
        (2 * fiberBandFreeMomentOrder m 168 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 168) + 1) +
          2 * fiberBandFreeMomentOrder m 168) <
      36 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hPpos) hP
  have hlogPLe :
    Nat.log2
        (2 * fiberBandFreeMomentOrder m 168 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 168) + 1) +
          2 * fiberBandFreeMomentOrder m 168) ≤
      35 :=
    Nat.le_of_lt_succ hlogP
  have hEpos : 0 < fiberBandFreeGrowthOrder m 168 ^ 2 * (m - 1) :=
    Nat.mul_pos (Nat.pow_pos (fiberBandFreeGrowthOrder_pos m 168)) hmlow
  have hEpow : fiberBandFreeGrowthOrder m 168 ^ 2 * (m - 1) < 2 ^ 33 := by
    calc
      _ ≤ 7782034889 := hE
      _ < 2 ^ 33 := by norm_num only
  have hlogE : Nat.log2 (fiberBandFreeGrowthOrder m 168 ^ 2 * (m - 1)) < 33 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hEpos) hEpow
  have hlogE' : Nat.log2 (fiberBandFreeGrowthOrder m 168 ^ 2 * (m - 1)) + 1 ≤ 33 :=
    Nat.succ_le_iff.mpr hlogE
  have hfirst : 2 * fiberBandFreeMomentOrder m 168 - 1 ≤ 1518225415 := by
    have h := Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hr) 1
    nlinarith only [h]
  nlinarith only [hfirst, hlogPLe, hlogE']

/-- For degrees from 2 through 42, free precision 164 gives the inner
double-exponential coefficient budget 1,446,789,710. -/
theorem fiberBandFree_orders_164_budget {m : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42) :
    2 * fiberBandFreeMomentOrder m 164 - 1 +
        Nat.log2
          (2 * fiberBandFreeMomentOrder m 164 *
              (Nat.log2 (2 * fiberBandFreeMomentOrder m 164) + 1) +
            2 * fiberBandFreeMomentOrder m 164) +
        Nat.log2 (fiberBandFreeGrowthOrder m 164 ^ 2 * (m - 1)) +
        1 +
        3 ≤
      1446789710 := by
  have hm1 : m - 1 ≤ 41 := Nat.sub_le_sub_right hhi 1
  have hmlow : 1 ≤ m - 1 := by
    have h := Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans hlo)
    nlinarith only [h, hlo]
  have hG : 164 * (m - 1) ≤ 6724 := by
    calc
      _ ≤ 164 * 41 := Nat.mul_le_mul_left 164 hm1
      _ = 6724 := by norm_num only
  have hn : fiberBandFreeGrowthOrder m 164 ≤ 13449 := by
    simp only [fiberBandFreeGrowthOrder]
    nlinarith only [hG]
  have hr : fiberBandFreeMomentOrder m 164 ≤ 723394820 := by
    simp only [fiberBandFreeMomentOrder]
    nlinarith only [hG]
  have hE : fiberBandFreeGrowthOrder m 164 ^ 2 * (m - 1) ≤ 7415899641 := by
    calc
      _ ≤ 13449 ^ 2 * 41 := Nat.mul_le_mul (Nat.pow_le_pow_left hn 2) hm1
      _ = 7415899641 := by norm_num only
  have h2r : 2 * fiberBandFreeMomentOrder m 164 < 2 ^ 31 := by
    calc
      _ ≤ 2 * 723394820 := Nat.mul_le_mul_left 2 hr
      _ < 2 ^ 31 := by norm_num only
  have hrpos : 0 < fiberBandFreeMomentOrder m 164 := fiberBandFreeMomentOrder_pos m 164
  have h2rpos : 0 < 2 * fiberBandFreeMomentOrder m 164 := Nat.mul_pos (by decide) hrpos
  have hlog2r : Nat.log2 (2 * fiberBandFreeMomentOrder m 164) < 31 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt h2rpos) h2r
  have hlog2r' : Nat.log2 (2 * fiberBandFreeMomentOrder m 164) + 1 ≤ 31 :=
    Nat.succ_le_iff.mpr hlog2r
  have hP :
    2 * fiberBandFreeMomentOrder m 164 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 164) + 1) +
        2 * fiberBandFreeMomentOrder m 164 <
      2 ^ 36 := by
    calc
      _ ≤ 2 * fiberBandFreeMomentOrder m 164 * 31 + 2 * fiberBandFreeMomentOrder m 164 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hlog2r') _
      _ ≤ 64 * 723394820 := by nlinarith only [hr]
      _ < 2 ^ 36 := by norm_num only
  have hPpos :
    0 <
      2 * fiberBandFreeMomentOrder m 164 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 164) + 1) +
        2 * fiberBandFreeMomentOrder m 164 :=
    lt_of_lt_of_le h2rpos (Nat.le_add_left _ _)
  have hlogP :
    Nat.log2
        (2 * fiberBandFreeMomentOrder m 164 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 164) + 1) +
          2 * fiberBandFreeMomentOrder m 164) <
      36 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hPpos) hP
  have hlogPLe :
    Nat.log2
        (2 * fiberBandFreeMomentOrder m 164 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 164) + 1) +
          2 * fiberBandFreeMomentOrder m 164) ≤
      35 :=
    Nat.le_of_lt_succ hlogP
  have hEpos : 0 < fiberBandFreeGrowthOrder m 164 ^ 2 * (m - 1) :=
    Nat.mul_pos (Nat.pow_pos (fiberBandFreeGrowthOrder_pos m 164)) hmlow
  have hEpow : fiberBandFreeGrowthOrder m 164 ^ 2 * (m - 1) < 2 ^ 33 := by
    calc
      _ ≤ 7415899641 := hE
      _ < 2 ^ 33 := by norm_num only
  have hlogE : Nat.log2 (fiberBandFreeGrowthOrder m 164 ^ 2 * (m - 1)) < 33 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hEpos) hEpow
  have hlogE' : Nat.log2 (fiberBandFreeGrowthOrder m 164 ^ 2 * (m - 1)) + 1 ≤ 33 :=
    Nat.succ_le_iff.mpr hlogE
  have hfirst : 2 * fiberBandFreeMomentOrder m 164 - 1 ≤ 1446789639 := by
    have h := Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hr) 1
    nlinarith only [h]
  nlinarith only [hfirst, hlogPLe, hlogE']

/-- For degrees from 2 through 42, free precision 280 gives a common inner
double-exponential coefficient budget of 4217292884. Bound the moment and
growth orders at degree 42, then control their binary logarithms by powers
of two. -/
theorem fiberBandFree_orders_280_budget {m : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42) :
    2 * fiberBandFreeMomentOrder m 280 - 1 +
        Nat.log2
          (2 * fiberBandFreeMomentOrder m 280 *
              (Nat.log2 (2 * fiberBandFreeMomentOrder m 280) + 1) +
            2 * fiberBandFreeMomentOrder m 280) +
        Nat.log2 (fiberBandFreeGrowthOrder m 280 ^ 2 * (m - 1)) +
        1 +
        3 ≤
      4217292884 := by
  have hm1 : m - 1 ≤ 41 := Nat.sub_le_sub_right hhi 1
  have hmlow : 1 ≤ m - 1 := by
    have h := Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans hlo)
    nlinarith only [h, hlo]
  have hG : 280 * (m - 1) ≤ 11480 := by
    calc
      _ ≤ 280 * 41 := Nat.mul_le_mul_left 280 hm1
      _ = 11480 := by norm_num only
  have hr : fiberBandFreeMomentOrder m 280 ≤ 2108646404 := by
    simp only [fiberBandFreeMomentOrder]
    nlinarith only [hG]
  have hn : fiberBandFreeGrowthOrder m 280 ≤ 22961 := by
    simp only [fiberBandFreeGrowthOrder]
    nlinarith only [hG]
  have hE : fiberBandFreeGrowthOrder m 280 ^ 2 * (m - 1) ≤ 21615508361 := by
    calc
      _ ≤ 22961 ^ 2 * 41 := Nat.mul_le_mul (Nat.pow_le_pow_left hn 2) hm1
      _ = 21615508361 := by norm_num only
  have h2r : 2 * fiberBandFreeMomentOrder m 280 < 2 ^ 33 := by
    calc
      _ ≤ 2 * 2108646404 := Nat.mul_le_mul_left 2 hr
      _ < 2 ^ 33 := by norm_num only
  have hrpos : 0 < fiberBandFreeMomentOrder m 280 := fiberBandFreeMomentOrder_pos m 280
  have h2rpos : 0 < 2 * fiberBandFreeMomentOrder m 280 := Nat.mul_pos (by decide) hrpos
  have hlog2r : Nat.log2 (2 * fiberBandFreeMomentOrder m 280) < 33 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt h2rpos) h2r
  have hlog2r' : Nat.log2 (2 * fiberBandFreeMomentOrder m 280) + 1 ≤ 33 :=
    Nat.succ_le_iff.mpr hlog2r
  have hP :
    2 * fiberBandFreeMomentOrder m 280 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 280) + 1) +
        2 * fiberBandFreeMomentOrder m 280 <
      2 ^ 38 := by
    calc
      _ ≤ 68 * 2108646404 := by nlinarith only [hr, hlog2r']
      _ < 2 ^ 38 := by norm_num only
  have hPpos :
    0 <
      2 * fiberBandFreeMomentOrder m 280 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 280) + 1) +
        2 * fiberBandFreeMomentOrder m 280 :=
    lt_of_lt_of_le h2rpos (Nat.le_add_left _ _)
  have hlogP :
    Nat.log2
        (2 * fiberBandFreeMomentOrder m 280 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 280) + 1) +
          2 * fiberBandFreeMomentOrder m 280) <
      38 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hPpos) hP
  have hlogP' :
    Nat.log2
        (2 * fiberBandFreeMomentOrder m 280 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 280) + 1) +
          2 * fiberBandFreeMomentOrder m 280) ≤
      37 :=
    Nat.le_of_lt_succ hlogP
  have hEpos : 0 < fiberBandFreeGrowthOrder m 280 ^ 2 * (m - 1) :=
    Nat.mul_pos (Nat.pow_pos (fiberBandFreeGrowthOrder_pos m 280)) hmlow
  have hEpow : fiberBandFreeGrowthOrder m 280 ^ 2 * (m - 1) < 2 ^ 35 := by
    calc
      _ ≤ 21615508361 := hE
      _ < 2 ^ 35 := by norm_num only
  have hlogE : Nat.log2 (fiberBandFreeGrowthOrder m 280 ^ 2 * (m - 1)) < 35 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hEpos) hEpow
  have hlogE' : Nat.log2 (fiberBandFreeGrowthOrder m 280 ^ 2 * (m - 1)) ≤ 34 :=
    Nat.le_of_lt_succ hlogE
  have hfirst : 2 * fiberBandFreeMomentOrder m 280 - 1 ≤ 4217292807 := by
    have h := Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hr) 1
    nlinarith only [h]
  nlinarith only [hfirst, hlogP', hlogE']

/-- Each degree from 2 through 42 at precision 280 fits the double-
exponential coefficient budget with inner exponent `B ≥ 4217292884`. -/
theorem fiberBandFreeCoefficient_280_le_double_exp {m B : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42)
    (hB : 4217292884 ≤ B) : fiberBandFreeCoefficient m 280 ≤ 2 ^ (2 ^ B) := by
  have hmlow : 1 ≤ m - 1 := Nat.sub_le_sub_right hlo 1
  have hG : 280 ≤ 280 * (m - 1) := Nat.mul_le_mul_left 280 hmlow
  have hr : 7 ≤ fiberBandFreeMomentOrder m 280 := by
    simp only [fiberBandFreeMomentOrder]
    nlinarith only [hG]
  have hEpos : 0 < fiberBandFreeGrowthOrder m 280 ^ 2 * (m - 1) :=
    Nat.mul_pos (Nat.pow_pos (fiberBandFreeGrowthOrder_pos m 280)) hmlow
  exact
    fiberBandFreeCoefficient_le_double_exp_of_quarter_budget_three hr hEpos
      ((fiberBandFree_orders_280_budget hlo hhi).trans hB)

/-- Every degree `2 ≤ m ≤ 42` at free precision 12 fits the inner budget
`7,746,111`. Bound the moment and growth orders at degree 42, then control
their binary logarithms by powers of two. -/
theorem fiberBandFree_orders_12_budget {m : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42) :
    2 * fiberBandFreeMomentOrder m 12 - 1 +
        Nat.log2
          (2 * fiberBandFreeMomentOrder m 12 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 12) + 1) +
            2 * fiberBandFreeMomentOrder m 12) +
        Nat.log2 (fiberBandFreeGrowthOrder m 12 ^ 2 * (m - 1)) +
        1 +
        3 ≤
      7746111 := by
  have hm1 : m - 1 ≤ 41 := Nat.sub_le_sub_right hhi 1
  have hmlow : 1 ≤ m - 1 := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide) hlo))
  have hG : 12 * (m - 1) ≤ 492 := by
    calc
      _ ≤ 12 * 41 := Nat.mul_le_mul_left 12 hm1
      _ = 492 := by norm_num only
  have hr : fiberBandFreeMomentOrder m 12 ≤ 3873028 := by
    simp only [fiberBandFreeMomentOrder]
    nlinarith only [hG]
  have hn : fiberBandFreeGrowthOrder m 12 ≤ 985 := by
    simp only [fiberBandFreeGrowthOrder]
    nlinarith only [hG]
  have hE : fiberBandFreeGrowthOrder m 12 ^ 2 * (m - 1) ≤ 39779225 := by
    calc
      _ ≤ 985 ^ 2 * 41 := Nat.mul_le_mul (Nat.pow_le_pow_left hn 2) hm1
      _ = 39779225 := by norm_num only
  have h2r : 2 * fiberBandFreeMomentOrder m 12 < 2 ^ 23 := by
    calc
      _ ≤ 2 * 3873028 := Nat.mul_le_mul_left 2 hr
      _ < 2 ^ 23 := by norm_num only
  have hrpos : 0 < fiberBandFreeMomentOrder m 12 := fiberBandFreeMomentOrder_pos m 12
  have h2rpos : 0 < 2 * fiberBandFreeMomentOrder m 12 := Nat.mul_pos (by decide) hrpos
  have hlog2r : Nat.log2 (2 * fiberBandFreeMomentOrder m 12) < 23 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt h2rpos) h2r
  have hlog2r' : Nat.log2 (2 * fiberBandFreeMomentOrder m 12) + 1 ≤ 23 := Nat.succ_le_iff.mpr hlog2r
  have hP :
    2 * fiberBandFreeMomentOrder m 12 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 12) + 1) +
        2 * fiberBandFreeMomentOrder m 12 <
      2 ^ 28 := by
    calc
      _ ≤ 2 * fiberBandFreeMomentOrder m 12 * 23 + 2 * fiberBandFreeMomentOrder m 12 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hlog2r') _
      _ ≤ 48 * 3873028 := by nlinarith only [hr]
      _ < 2 ^ 28 := by norm_num only
  have hPpos :
    0 <
      2 * fiberBandFreeMomentOrder m 12 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 12) + 1) +
        2 * fiberBandFreeMomentOrder m 12 :=
    lt_of_lt_of_le h2rpos (Nat.le_add_left _ _)
  have hlogP :
    Nat.log2
        (2 * fiberBandFreeMomentOrder m 12 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 12) + 1) +
          2 * fiberBandFreeMomentOrder m 12) <
      28 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hPpos) hP
  have hlogP' :
    Nat.log2
        (2 * fiberBandFreeMomentOrder m 12 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 12) + 1) +
          2 * fiberBandFreeMomentOrder m 12) ≤
      27 :=
    Nat.le_of_lt_succ hlogP
  have hEpos : 0 < fiberBandFreeGrowthOrder m 12 ^ 2 * (m - 1) :=
    Nat.mul_pos (Nat.pow_pos (fiberBandFreeGrowthOrder_pos m 12)) hmlow
  have hEpow : fiberBandFreeGrowthOrder m 12 ^ 2 * (m - 1) < 2 ^ 26 := by
    calc
      _ ≤ 39779225 := hE
      _ < 2 ^ 26 := by norm_num only
  have hlogE : Nat.log2 (fiberBandFreeGrowthOrder m 12 ^ 2 * (m - 1)) < 26 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hEpos) hEpow
  have hlogE' : Nat.log2 (fiberBandFreeGrowthOrder m 12 ^ 2 * (m - 1)) ≤ 25 :=
    Nat.le_of_lt_succ hlogE
  have hfirst : 2 * fiberBandFreeMomentOrder m 12 - 1 ≤ 7746055 := by
    have h := Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hr) 1
    nlinarith only [h]
  nlinarith only [hfirst, hlogP', hlogE']

/-- Every degree `2 ≤ m ≤ 42` at free precision 18 fits the inner budget
`17,428,673`. Bound the moment and growth orders at degree 42, then control
their binary logarithms by powers of two. -/
theorem fiberBandFree_orders_18_budget {m : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42) :
    2 * fiberBandFreeMomentOrder m 18 - 1 +
        Nat.log2
          (2 * fiberBandFreeMomentOrder m 18 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 18) + 1) +
            2 * fiberBandFreeMomentOrder m 18) +
        Nat.log2 (fiberBandFreeGrowthOrder m 18 ^ 2 * (m - 1)) +
        1 +
        3 ≤
      17428673 := by
  have hm1 : m - 1 ≤ 41 := Nat.sub_le_sub_right hhi 1
  have hmlow : 1 ≤ m - 1 := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide) hlo))
  have hG : 18 * (m - 1) ≤ 738 := by
    calc
      _ ≤ 18 * 41 := Nat.mul_le_mul_left 18 hm1
      _ = 738 := by norm_num only
  have hr : fiberBandFreeMomentOrder m 18 ≤ 8714308 := by
    simp only [fiberBandFreeMomentOrder]
    nlinarith only [hG]
  have hn : fiberBandFreeGrowthOrder m 18 ≤ 1477 := by
    simp only [fiberBandFreeGrowthOrder]
    nlinarith only [hG]
  have hE : fiberBandFreeGrowthOrder m 18 ^ 2 * (m - 1) ≤ 89442689 := by
    calc
      _ ≤ 1477 ^ 2 * 41 := Nat.mul_le_mul (Nat.pow_le_pow_left hn 2) hm1
      _ = 89442689 := by norm_num only
  have h2r : 2 * fiberBandFreeMomentOrder m 18 < 2 ^ 25 := by
    calc
      _ ≤ 2 * 8714308 := Nat.mul_le_mul_left 2 hr
      _ < 2 ^ 25 := by norm_num only
  have hrpos : 0 < fiberBandFreeMomentOrder m 18 := fiberBandFreeMomentOrder_pos m 18
  have h2rpos : 0 < 2 * fiberBandFreeMomentOrder m 18 := Nat.mul_pos (by decide) hrpos
  have hlog2r : Nat.log2 (2 * fiberBandFreeMomentOrder m 18) < 25 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt h2rpos) h2r
  have hlog2r' : Nat.log2 (2 * fiberBandFreeMomentOrder m 18) + 1 ≤ 25 := Nat.succ_le_iff.mpr hlog2r
  have hP :
    2 * fiberBandFreeMomentOrder m 18 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 18) + 1) +
        2 * fiberBandFreeMomentOrder m 18 <
      2 ^ 29 := by
    calc
      _ ≤ 2 * fiberBandFreeMomentOrder m 18 * 25 + 2 * fiberBandFreeMomentOrder m 18 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hlog2r') _
      _ ≤ 52 * 8714308 := by nlinarith only [hr]
      _ < 2 ^ 29 := by norm_num only
  have hPpos :
    0 <
      2 * fiberBandFreeMomentOrder m 18 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 18) + 1) +
        2 * fiberBandFreeMomentOrder m 18 :=
    lt_of_lt_of_le h2rpos (Nat.le_add_left _ _)
  have hlogP :
    Nat.log2
        (2 * fiberBandFreeMomentOrder m 18 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 18) + 1) +
          2 * fiberBandFreeMomentOrder m 18) <
      29 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hPpos) hP
  have hlogP' :
    Nat.log2
        (2 * fiberBandFreeMomentOrder m 18 * (Nat.log2 (2 * fiberBandFreeMomentOrder m 18) + 1) +
          2 * fiberBandFreeMomentOrder m 18) ≤
      28 :=
    Nat.le_of_lt_succ hlogP
  have hEpos : 0 < fiberBandFreeGrowthOrder m 18 ^ 2 * (m - 1) :=
    Nat.mul_pos (Nat.pow_pos (fiberBandFreeGrowthOrder_pos m 18)) hmlow
  have hEpow : fiberBandFreeGrowthOrder m 18 ^ 2 * (m - 1) < 2 ^ 27 := by
    calc
      _ ≤ 89442689 := hE
      _ < 2 ^ 27 := by norm_num only
  have hlogE : Nat.log2 (fiberBandFreeGrowthOrder m 18 ^ 2 * (m - 1)) < 27 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt hEpos) hEpow
  have hlogE' : Nat.log2 (fiberBandFreeGrowthOrder m 18 ^ 2 * (m - 1)) ≤ 26 :=
    Nat.le_of_lt_succ hlogE
  have hfirst : 2 * fiberBandFreeMomentOrder m 18 - 1 ≤ 17428615 := by
    have h := Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hr) 1
    nlinarith only [h]
  nlinarith only [hfirst, hlogP', hlogE']

/-- At free precision 12, every degree from 2 through 42 fits the double-
exponential coefficient budget `2^(2^B)` for `B ≥ 7,746,111`. -/
theorem fiberBandFreeCoefficient_12_le_double_exp {m B : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42)
    (hB : 7746111 ≤ B) : fiberBandFreeCoefficient m 12 ≤ 2 ^ (2 ^ B) := by
  have hmlow : 1 ≤ m - 1 := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide) hlo))
  have hGlo : 12 ≤ 12 * (m - 1) := Nat.mul_le_mul_left 12 hmlow
  have hr : 7 ≤ fiberBandFreeMomentOrder m 12 := by
    simp only [fiberBandFreeMomentOrder]
    nlinarith only [hGlo]
  have hEpos : 0 < fiberBandFreeGrowthOrder m 12 ^ 2 * (m - 1) :=
    Nat.mul_pos (Nat.pow_pos (fiberBandFreeGrowthOrder_pos m 12)) hmlow
  exact
    fiberBandFreeCoefficient_le_double_exp_of_quarter_budget_three hr hEpos
      ((fiberBandFree_orders_12_budget hlo hhi).trans hB)

/-- At free precision 18, every degree from 2 through 42 fits the double-
exponential coefficient budget `2^(2^B)` for `B ≥ 17,428,673`. -/
theorem fiberBandFreeCoefficient_18_le_double_exp {m B : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42)
    (hB : 17428673 ≤ B) : fiberBandFreeCoefficient m 18 ≤ 2 ^ (2 ^ B) := by
  have hmlow : 1 ≤ m - 1 := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide) hlo))
  have hGlo : 18 ≤ 18 * (m - 1) := Nat.mul_le_mul_left 18 hmlow
  have hr : 7 ≤ fiberBandFreeMomentOrder m 18 := by
    simp only [fiberBandFreeMomentOrder]
    nlinarith only [hGlo]
  have hEpos : 0 < fiberBandFreeGrowthOrder m 18 ^ 2 * (m - 1) :=
    Nat.mul_pos (Nat.pow_pos (fiberBandFreeGrowthOrder_pos m 18)) hmlow
  exact
    fiberBandFreeCoefficient_le_double_exp_of_quarter_budget_three hr hEpos
      ((fiberBandFree_orders_18_budget hlo hhi).trans hB)

/-- Every degree from 2 through 42 at precision 162 fits any coefficient
budget whose inner exponent is at least 1411717327. -/
theorem fiberBandFreeCoefficient_162_le_double_exp {m B : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42)
    (hB : 1411717327 ≤ B) : fiberBandFreeCoefficient m 162 ≤ 2 ^ (2 ^ B) := by
  have hmlow : 1 ≤ m - 1 := by
    have h := Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans hlo)
    nlinarith only [h, hlo]
  have hGlo : 162 ≤ 162 * (m - 1) := Nat.mul_le_mul_left 162 hmlow
  have hr : 7 ≤ fiberBandFreeMomentOrder m 162 := by
    simp only [fiberBandFreeMomentOrder]
    nlinarith only [hGlo]
  have hepos : 0 < fiberBandFreeGrowthOrder m 162 ^ 2 * (m - 1) := by
    have hG : 0 < fiberBandFreeGrowthOrder m 162 := by
      simp only [fiberBandFreeGrowthOrder]
      omega
    have hm : 0 < m - 1 := by omega
    exact Nat.mul_pos (Nat.pow_pos hG) hm
  have hbudget := fiberBandFree_orders_162_budget hlo hhi
  exact fiberBandFreeCoefficient_le_double_exp_of_quarter_budget_three hr hepos (hbudget.trans hB)

/-- Every degree from 2 through 42 at precision 168 fits the common inner
budget 2^(2^B) for B ≥ 1,518,225,486. -/
theorem fiberBandFreeCoefficient_168_le_double_exp {m B : ℕ} (hlo : 2 ≤ m) (hhi : m ≤ 42)
    (hB : 1518225486 ≤ B) : fiberBandFreeCoefficient m 168 ≤ 2 ^ (2 ^ B) := by
  have hmlow : 1 ≤ m - 1 := Nat.sub_le_sub_right hlo 1
  have hG : 168 ≤ 168 * (m - 1) := Nat.mul_le_mul_left 168 hmlow
  have hr : 7 ≤ fiberBandFreeMomentOrder m 168 := by
    simp only [fiberBandFreeMomentOrder]
    nlinarith only [hG]
  have hEpos : 0 < fiberBandFreeGrowthOrder m 168 ^ 2 * (m - 1) :=
    Nat.mul_pos (Nat.pow_pos (fiberBandFreeGrowthOrder_pos m 168)) hmlow
  exact
    fiberBandFreeCoefficient_le_double_exp_of_quarter_budget_three hr hEpos
      ((fiberBandFree_orders_168_budget hlo hhi).trans hB)

/-- The alternative degree constants have a common sum over the eight fixed
degrees. The extra one handles the trivial small-height estimate. -/
def eightDegreeFreeFiberCoefficient (c : ℕ) : ℕ :=
  1 + ∑ m ∈ ({6, 7, 8, 9, 11, 14, 21, 42} : Finset ℕ), fiberBandFreeCoefficient m c

/-- The free-order coefficient controls each balanced height band. Use the
explicit orders, the exact strict height gap, and the natural root estimate;
the factorial remains symbolic in the returned coefficient. -/
theorem heightRestrictedRatioSet_le_explicit_free_fiber_band_bound {m c : ℕ} (hm : 0 < m)
    (hc : 0 < c) :
    ∀ (p H T : ℕ) [Fact p.Prime],
      H < p →
        0 < T →
        ∀ beta : ℝ,
          (p : ℝ) ≤ (T : ℝ) ^ m * (p : ℝ) ^ (m * beta) →
            (T : ℝ) ^ m ≤ (p : ℝ) * (p : ℝ) ^ (m * beta) →
            ((heightRestrictedRatioSet p H T).card : ℝ) ≤
              fiberBandFreeCoefficient m c * (T : ℝ) ^ (1 + 1 / (c : ℝ)) * (p : ℝ) ^ beta := by
  let n := fiberBandFreeGrowthOrder m c
  let r := fiberBandFreeMomentOrder m c
  have hn : 0 < n := fiberBandFreeGrowthOrder_pos m c
  have hr : 0 < r := fiberBandFreeMomentOrder_pos m c
  have hl : c * heightRatioLossExponent m n r < n * m * r := by
    simpa only [n, r] using fiberBandFree_parameters_small_loss hm
  let D := quotientPowerBoundConstant r ^ (n ^ 2 * (m - 1))
  let C : ℕ := 5 * (D + 1) + 1
  intro p H T hp hHp hT beta hlo hhi
  change
    ((heightRestrictedRatioSet p H T).card : ℝ) ≤
      (C : ℝ) * (T : ℝ) ^ (1 + 1 / (c : ℝ)) * (p : ℝ) ^ beta
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hT1 : (1 : ℝ) ≤ T := Nat.one_le_cast.mpr hT
  have hnr := Nat.mul_pos hn hr
  have hnrR : (0 : ℝ) < (n * r : ℕ) := Nat.cast_pos.mpr hnr
  have hcR : (0 : ℝ) < c := Nat.cast_pos.mpr hc
  have hpoly := heightRestrictedRatioSet_fiber_power_le_polynomial hHp hT hm hn hr
  have hb := natural_count_le_polynomial_root hnr hpoly
  have he : ((n * r : ℕ) : ℝ) / (n * r : ℕ) = 1 := div_self (ne_of_gt hnrR)
  rw [he, Real.rpow_one] at hb
  have hL : (heightRatioLossExponent m n r : ℝ) / (n * r : ℕ) ≤ (m : ℝ) / c := by
    apply (div_le_div_iff₀ hnrR hcR).mpr
    have h := Nat.cast_le (α := ℝ).mpr hl.le
    simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using h
  have ht := Real.rpow_le_rpow_of_exponent_le hT1 hL
  have hband := residue_product_band_bound hlo hhi
  have hb' :
    ((heightRestrictedRatioSet p H T).card : ℝ) ^ m * p ≤
      (D + 1 : ℕ) * (T : ℝ) ^ ((m : ℝ) / c) *
        (5 * (p : ℝ) * (T : ℝ) ^ m * (p : ℝ) ^ (m * beta)) := by
    have hh :=
      mul_le_mul (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (D + 1))) hband
        (Nat.cast_nonneg (p ^ 2 + 4 * T ^ (2 * m)))
        (mul_nonneg (Nat.cast_nonneg (D + 1)) (Real.rpow_nonneg (Nat.cast_nonneg T) _))
    have hb0 :
      ((heightRestrictedRatioSet p H T).card : ℝ) ^ m * p ≤
        (D + 1 : ℕ) * (T : ℝ) ^ ((heightRatioLossExponent m n r : ℝ) / (n * r : ℕ)) *
          ((p ^ 2 + 4 * T ^ (2 * m) : ℕ) : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_pow, D] using hb
    exact hb0.trans hh
  have hCpow : (5 * (D + 1 : ℕ) : ℝ) ≤ (C : ℝ) ^ m := by
    have hpow := Nat.pow_le_pow_right (Nat.succ_pos (5 * (D + 1))) hm
    have hnat : 5 * (D + 1) ≤ C ^ m := (Nat.le_succ _).trans (by simpa only [pow_one] using hpow)
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr hnat
  have heT : ((T : ℝ) ^ (1 + 1 / (c : ℝ))) ^ m = (T : ℝ) ^ ((m : ℝ) / c) * (T : ℝ) ^ m := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg T), ← Real.rpow_natCast, ←
      Real.rpow_add (Nat.cast_pos.mpr hT)]
    congr 1
    ring
  have hep : ((p : ℝ) ^ beta) ^ m = (p : ℝ) ^ ((m : ℝ) * beta) := by
    rw [← Real.rpow_mul_natCast hpR.le]
    congr 1
    ring
  apply
    (pow_le_pow_iff_left₀ (Nat.cast_nonneg _)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg C) (Real.rpow_nonneg (Nat.cast_nonneg T) _))
          (Real.rpow_nonneg hpR.le _))
        (ne_of_gt hm)).mp
  rw [mul_pow, mul_pow, heT, hep]
  have hcoeff :=
    mul_le_mul_of_nonneg_right hCpow
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg T) ((m : ℝ) / c))
          (pow_nonneg (Nat.cast_nonneg T) m))
        (Real.rpow_nonneg hpR.le ((m : ℝ) * beta)))
  apply (mul_le_mul_iff_left₀ hpR).mp
  calc
    _ ≤ _ := hb'
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hcoeff hpR.le
      simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using hh

/-- The sum of the eight free-order degree coefficients bounds every
restricted ratio below $p^{5/28}$. Sum the degree bands and use the trivial
positive-rational count below $p^{1/84}$. -/
theorem heightRestrictedRatioSet_le_explicit_free_eight_degree_bound {c : ℕ} (hc : 0 < c) :
    ∀ (p H T : ℕ) [Fact p.Prime],
      H < p →
        (T : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ) →
        ((heightRestrictedRatioSet p H T).card : ℝ) ≤
          eightDegreeFreeFiberCoefficient c * (T : ℝ) ^ (1 + 1 / (c : ℝ)) *
            (p : ℝ) ^ (1 / 84 : ℝ) := by
  classical
  let D : Finset ℕ := {6, 7, 8, 9, 11, 14, 21, 42}
  have hD : ∀ m : D, 0 < m.val := by
    intro m
    have hh := m.property
    simp only [D, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with h | h | h | h | h | h | h | h
    all_goals rw [h]; decide
  let C : D → ℝ := fun m ↦ fiberBandFreeCoefficient m.val c
  have hC (m : D) : 0 < C m := by
    dsimp only [C]
    exact Nat.cast_pos.mpr (Nat.succ_pos _)
  have hbound (m : D) := heightRestrictedRatioSet_le_explicit_free_fiber_band_bound (hD m) hc
  let K : ℝ := 1 + ∑ m : D, C m
  have hsum : 0 ≤ ∑ m : D, C m := Finset.sum_nonneg (fun m _ ↦ (hC m).le)
  have hK : 1 ≤ K := by
    dsimp only [K]; linarith only [hsum]
  have hCK (m : D) : C m ≤ K := by
    have h := Finset.single_le_sum (s := Finset.univ) (fun i _ ↦ (hC i).le) (Finset.mem_univ m)
    dsimp only [K]
    linarith only [h]
  have hKdef : (eightDegreeFreeFiberCoefficient c : ℝ) = K := by
    simp only [eightDegreeFreeFiberCoefficient, K, C, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
    rw [Finset.sum_coe_sort D (fun m : ℕ ↦ (fiberBandFreeCoefficient m c : ℝ))]
  rw [hKdef]
  intro p H T hp hHp htop
  have hcanonical : ∀ q ∈ heightRestrictedRatioSet p H T, 0 < q ∧ q.num.natAbs ≤ T ∧ q.den ≤ T :=
    fun q hq ↦
    boundedRationalResidue_canonical_height
      (Exists.choose_spec (heightRestrictedRatioSet_has_residues hHp q hq))
  have htriv := Nat.cast_le (α := ℝ).mpr (bounded_positive_rational_card_le_square _ hcanonical)
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := lt_trans (by norm_num only : (0 : ℝ) < 1) hp1
  have hpw : 0 ≤ (p : ℝ) ^ (1 / 84 : ℝ) := Real.rpow_nonneg hp0.le _
  by_cases hT : T = 0
  · subst T
    have hc0 : (0 : ℝ) < 1 + 1 / (c : ℝ) :=
      add_pos_of_pos_of_nonneg (by norm_num only)
        (div_nonneg (by norm_num only) (Nat.cast_nonneg c))
    simpa only [Nat.zero_pow (by decide : 0 < 2), Nat.cast_zero, Real.zero_rpow (ne_of_gt hc0),
      mul_zero, zero_mul] using htriv
  have hTpos : 0 < T := Nat.pos_of_ne_zero hT
  have hT1 : (1 : ℝ) ≤ T := Nat.one_le_cast.mpr hTpos
  have hT0 : (0 : ℝ) < T := Nat.cast_pos.mpr hTpos
  have hTex : (T : ℝ) ≤ (T : ℝ) ^ (1 + 1 / (c : ℝ)) := by
    have he : (1 : ℝ) ≤ 1 + 1 / (c : ℝ) :=
      le_add_of_nonneg_right (div_nonneg (by norm_num only) (Nat.cast_nonneg c))
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT1 he
  by_cases hsmall : (T : ℝ) ≤ (p : ℝ) ^ (1 / 84 : ℝ)
  · have h1 := mul_le_mul_of_nonneg_left hsmall hT0.le
    have h2 := mul_le_mul_of_nonneg_right hTex hpw
    have h3 :=
      mul_le_mul_of_nonneg_right hK (mul_nonneg (Real.rpow_nonneg hT0.le (1 + 1 / (c : ℝ))) hpw)
    have htriv' : ((heightRestrictedRatioSet p H T).card : ℝ) ≤ (T : ℝ) ^ 2 := by
      simpa only [Nat.cast_pow] using htriv
    calc
      _ ≤ _ := htriv'
      _ ≤ (T : ℝ) * (p : ℝ) ^ (1 / 84 : ℝ) := by simpa only [pow_two] using h1
      _ ≤ (T : ℝ) ^ (1 + 1 / (c : ℝ)) * (p : ℝ) ^ (1 / 84 : ℝ) := h2
      _ ≤ _ := by simpa only [one_mul, mul_assoc] using h3
  let alpha : ℝ := Real.log T / Real.log p
  have heq : (T : ℝ) = (p : ℝ) ^ alpha := by
    rw [Real.rpow_def_of_pos hp0]
    dsimp only [alpha]
    rw [mul_div_cancel₀ (Real.log T) (ne_of_gt (Real.log_pos hp1)), Real.exp_log hT0]
  have halphaLo : (1 / 84 : ℝ) ≤ alpha :=
    ((Real.rpow_le_rpow_left_iff hp1).mp
      (by
        rw [← heq]; exact (not_le.mp hsmall).le))
  have halphaHi : alpha ≤ (5 / 28 : ℝ) :=
    (Real.rpow_le_rpow_left_iff hp1).mp
      (by
        rw [← heq]; exact htop)
  obtain ⟨m, hm, hlo, hhi⟩ := eight_degree_exponent_cover halphaLo halphaHi
  let i : D := ⟨m, hm⟩
  have hb := residue_band_of_power_height (Fact.out : p.Prime).one_lt (hD i) heq hlo hhi
  have hcount := hbound i p H T hHp hTpos (1 / 84) hb.1 hb.2
  have hfactor : 0 ≤ (T : ℝ) ^ (1 + 1 / (c : ℝ)) * (p : ℝ) ^ (1 / 84 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hT0.le _) hpw
  exact hcount.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hCK i) hfactor)

/-- Natural coefficient for the complete congruence count with independent
count-loss parameter `h`. The harmonic factor is `2h+1`; the height precision
`c` is selected separately through `eightDegreeFreeFiberCoefficient`. -/
def freeFiniteFiberCountCoefficient (c h : ℕ) : ℕ :=
  4 * eightDegreeFreeFiberCoefficient c * (2 * h + 1)

/-- The total independent-loss count coefficient is below the next double
exponential when all eight free degree coefficients fit a common budget.
Combine the eight-term sum with its harmonic multiplier before absorbing them. -/
theorem freeFiniteFiberCountCoefficient_lt_double_exp_of_degree_bounds {c h B : ℕ}
    (hfactor : 36 * (2 * h + 1) < 2 ^ (2 ^ B))
    (hF :
      ∀ m ∈ ({6, 7, 8, 9, 11, 14, 21, 42} : Finset ℕ), fiberBandFreeCoefficient m c ≤ 2 ^ (2 ^ B)) :
    freeFiniteFiberCountCoefficient c h < 2 ^ (2 ^ (B + 1)) := by
  let D : Finset ℕ := {6, 7, 8, 9, 11, 14, 21, 42}
  let U : ℕ := 2 ^ (2 ^ B)
  have hU : 1 ≤ U := Nat.one_le_pow _ _ (by decide : 0 < 2)
  have hF' : ∀ m ∈ D, fiberBandFreeCoefficient m c ≤ U := by
    intro m hm
    exact hF m (by simpa only [D] using hm)
  have hs :=
    one_add_sum_le_card_budget D (fun m ↦ fiberBandFreeCoefficient m c) (k := 8) (by decide) hU hF'
  have hK : eightDegreeFreeFiberCoefficient c ≤ 9 * U := by
    change 1 + ∑ m ∈ D, fiberBandFreeCoefficient m c ≤ 9 * U
    exact hs
  have hC : freeFiniteFiberCountCoefficient c h ≤ (36 * (2 * h + 1)) * U := by
    unfold freeFiniteFiberCountCoefficient
    calc
      _ = (4 * (2 * h + 1)) * eightDegreeFreeFiberCoefficient c := by ring
      _ ≤ (4 * (2 * h + 1)) * (9 * U) := Nat.mul_le_mul_left _ hK
      _ = (36 * (2 * h + 1)) * U := by ring
  exact hC.trans_lt (mul_lt_double_exp_succ hfactor)

/-- The complete count coefficient at precision 280 and loss 140 fits the
next double-exponential budget once the inner exponent is at least
4,217,292,884. Sum the eight degree bounds and absorb the harmonic factor. -/
theorem freeFiniteFiberCountCoefficient_280_140_lt_double_exp {B : ℕ} (hB : 4217292884 ≤ B) :
    freeFiniteFiberCountCoefficient 280 140 < 2 ^ (2 ^ (B + 1)) := by
  apply freeFiniteFiberCountCoefficient_lt_double_exp_of_degree_bounds
  · have hB4 : 4 ≤ B := (by norm_num only : 4 ≤ 4217292884).trans hB
    have h2B : 16 ≤ 2 ^ B := Nat.pow_le_pow_right (by decide : 0 < 2) hB4
    have hUnit : 2 ^ 16 ≤ 2 ^ (2 ^ B) := Nat.pow_le_pow_right (by decide : 0 < 2) h2B
    calc
      36 * (2 * 140 + 1) = 10116 := by norm_num only
      _ < 2 ^ 16 := by norm_num only
      _ ≤ 2 ^ (2 ^ B) := hUnit
  · intro m hm
    have hm' : m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 11 ∨ m = 14 ∨ m = 21 ∨ m = 42 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      exact
        fiberBandFreeCoefficient_280_le_double_exp (B := B) (by norm_num only) (by norm_num only) hB

/-- The complete count coefficient at free precision 20 and independent loss
10 is below the next double-exponential budget. Bound the eight degrees by
their shared budget and absorb the fixed harmonic factor. -/
theorem freeFiniteFiberCountCoefficient_20_10_lt_double_exp {B : ℕ} (hB : 21516867 ≤ B) :
    freeFiniteFiberCountCoefficient 20 10 < 2 ^ (2 ^ (B + 1)) := by
  apply freeFiniteFiberCountCoefficient_lt_double_exp_of_degree_bounds
  · have hB4 : 4 ≤ B := (by norm_num only : 4 ≤ 21516867).trans hB
    calc
      36 * (2 * 10 + 1) = 756 := by norm_num only
      _ < 5796 := by norm_num only
      _ < 2 ^ (2 ^ B) := finiteFiberCount_harmonic_factor_lt_unit hB4
  · intro m hm
    have hm' : m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 11 ∨ m = 14 ∨ m = 21 ∨ m = 42 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      exact
        (fiberBandFreeCoefficient_20_le_double_exp (B := B) (by norm_num only) (by norm_num only)
          hB)

/-- The complete count coefficient at precision 162 and independent loss 81
fits the next double-exponential budget after summing the eight degrees. -/
theorem freeFiniteFiberCountCoefficient_162_81_lt_double_exp {B : ℕ} (hB : 1411717327 ≤ B) :
    freeFiniteFiberCountCoefficient 162 81 < 2 ^ (2 ^ (B + 1)) := by
  apply freeFiniteFiberCountCoefficient_lt_double_exp_of_degree_bounds
  · have hB4 : 4 ≤ B := (by norm_num only : 4 ≤ 1411717327).trans hB
    have h2B : 16 ≤ 2 ^ B := Nat.pow_le_pow_right (by decide : 0 < 2) hB4
    have hUnit : 2 ^ 16 ≤ 2 ^ (2 ^ B) := Nat.pow_le_pow_right (by decide : 0 < 2) h2B
    calc
      36 * (2 * 81 + 1) = 5868 := by norm_num only
      _ < 2 ^ 16 := by norm_num only
      _ ≤ 2 ^ (2 ^ B) := hUnit
  · intro m hm
    have hm' : m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 11 ∨ m = 14 ∨ m = 21 ∨ m = 42 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      exact
        (fiberBandFreeCoefficient_162_le_double_exp (B := B) (by norm_num only) (by norm_num only)
          hB)

/-- The complete finite-fiber count coefficient at precision 168 and
independent loss 84 fits below 2^(2^(B+1)) for B ≥ 1,518,225,486. -/
theorem freeFiniteFiberCountCoefficient_168_84_lt_double_exp {B : ℕ} (hB : 1518225486 ≤ B) :
    freeFiniteFiberCountCoefficient 168 84 < 2 ^ (2 ^ (B + 1)) := by
  apply freeFiniteFiberCountCoefficient_lt_double_exp_of_degree_bounds
  · have hB4 : 4 ≤ B := (by norm_num only : 4 ≤ 1518225486).trans hB
    have h2B : 16 ≤ 2 ^ B := Nat.pow_le_pow_right (by decide : 0 < 2) hB4
    have hUnit : 2 ^ 16 ≤ 2 ^ (2 ^ B) := Nat.pow_le_pow_right (by decide : 0 < 2) h2B
    calc
      36 * (2 * 84 + 1) = 6084 := by norm_num only
      _ < 2 ^ 16 := by norm_num only
      _ ≤ 2 ^ (2 ^ B) := hUnit
  · intro m hm
    have hm' : m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 11 ∨ m = 14 ∨ m = 21 ∨ m = 42 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      apply fiberBandFreeCoefficient_le_double_exp_of_quarter_budget_three
      · norm_num only [fiberBandFreeMomentOrder]
      · norm_num only [fiberBandFreeGrowthOrder]
      · exact (fiberBandFree_orders_168_budget (by norm_num only) (by norm_num only)).trans hB

/-- The complete finite-fiber count coefficient at precision 164 and
independent loss 82 fits the double-exponential budget at `B = 1,446,789,710`.
-/
theorem freeFiniteFiberCountCoefficient_164_82_lt_double_exp {B : ℕ} (hB : 1446789710 ≤ B) :
    freeFiniteFiberCountCoefficient 164 82 < 2 ^ (2 ^ (B + 1)) := by
  apply freeFiniteFiberCountCoefficient_lt_double_exp_of_degree_bounds
  · have hB4 : 4 ≤ B := (by norm_num only : 4 ≤ 1446789710).trans hB
    have h2B : 16 ≤ 2 ^ B := Nat.pow_le_pow_right (by decide : 0 < 2) hB4
    have hUnit : 2 ^ 16 ≤ 2 ^ (2 ^ B) := Nat.pow_le_pow_right (by decide : 0 < 2) h2B
    calc
      36 * (2 * 82 + 1) = 5940 := by norm_num only
      _ < 2 ^ 16 := by norm_num only
      _ ≤ 2 ^ (2 ^ B) := hUnit
  · intro m hm
    have hm' : m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 11 ∨ m = 14 ∨ m = 21 ∨ m = 42 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      apply fiberBandFreeCoefficient_le_double_exp_of_quarter_budget_three
      · norm_num only [fiberBandFreeMomentOrder]
      · norm_num only [fiberBandFreeGrowthOrder]
      · exact (fiberBandFree_orders_164_budget (by norm_num only) (by norm_num only)).trans hB

/-- The complete count coefficient at precision 12 and independent loss 6 is
below `2^(2^(B+1))` whenever `B ≥ 7,746,111`. -/
theorem freeFiniteFiberCountCoefficient_12_6_lt_double_exp {B : ℕ} (hB : 7746111 ≤ B) :
    freeFiniteFiberCountCoefficient 12 6 < 2 ^ (2 ^ (B + 1)) := by
  apply freeFiniteFiberCountCoefficient_lt_double_exp_of_degree_bounds
  · have hB4 : 4 ≤ B := (by norm_num only : 4 ≤ 7746111).trans hB
    calc
      36 * (2 * 6 + 1) = 468 := by norm_num only
      _ < 5796 := by norm_num only
      _ < 2 ^ (2 ^ B) := finiteFiberCount_harmonic_factor_lt_unit hB4
  · intro m hm
    have hm' : m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 11 ∨ m = 14 ∨ m = 21 ∨ m = 42 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      exact fiberBandFreeCoefficient_12_le_double_exp (by norm_num only) (by norm_num only) hB

/-- The complete count coefficient at precision 18 and independent loss 9 is
below `2^(2^(B+1))` whenever `B ≥ 17,428,673`. -/
theorem freeFiniteFiberCountCoefficient_18_9_lt_double_exp {B : ℕ} (hB : 17428673 ≤ B) :
    freeFiniteFiberCountCoefficient 18 9 < 2 ^ (2 ^ (B + 1)) := by
  apply freeFiniteFiberCountCoefficient_lt_double_exp_of_degree_bounds
  · have hB4 : 4 ≤ B := (by norm_num only : 4 ≤ 17428673).trans hB
    calc
      36 * (2 * 9 + 1) = 684 := by norm_num only
      _ < 5796 := by norm_num only
      _ < 2 ^ (2 ^ B) := finiteFiberCount_harmonic_factor_lt_unit hB4
  · intro m hm
    have hm' : m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 11 ∨ m = 14 ∨ m = 21 ∨ m = 42 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    rcases hm' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      exact fiberBandFreeCoefficient_18_le_double_exp (by norm_num only) (by norm_num only) hB

/-- Raise a complete-count coefficient through the energy power and absorb
the fixed coefficient `2^176` into the symbolic prime threshold. -/
theorem free_finite_fiber_energy_coefficient_lt_prime_threshold {a B u c h : ℕ}
    (hcount : freeFiniteFiberCountCoefficient c h < 2 ^ (2 ^ (B + 1)))
    (hbudget : B + 1 + 13 * a + 176 * a < u) :
    (2 ^ 176 : ℕ) ^ a * freeFiniteFiberCountCoefficient c h ^ (13 * a) <
      explicitFiniteFiberPrimeThreshold u := by
  have hA : (2 ^ 176 : ℕ) ^ a ≤ 2 ^ (176 * a) := by rw [← pow_mul]
  exact mul_power_lt_double_exp_of_budget hcount.le hA hbudget

/-- The precision-20, loss-10 count coefficient supports the explicit
energy coefficient at prime threshold `P(21518759)`. -/
theorem free_finite_fiber_energy_coefficient_lt_prime_threshold_20 :
    (2 ^ 176 : ℕ) ^ 10 * freeFiniteFiberCountCoefficient 20 10 ^ (13 * 10) <
      explicitFiniteFiberPrimeThreshold 21518759 := by
  apply
    free_finite_fiber_energy_coefficient_lt_prime_threshold (a := 10) (B := 21516867) (u :=
      21518759) (c := 20) (h := 10)
  · exact freeFiniteFiberCountCoefficient_20_10_lt_double_exp (by norm_num only)
  · norm_num only

/-- The precision-162, loss-81 count coefficient supports the explicit
energy coefficient at prime threshold `P(1411732827)`. -/
theorem free_finite_fiber_energy_coefficient_lt_prime_threshold_162 :
    (2 ^ 176 : ℕ) ^ 82 * freeFiniteFiberCountCoefficient 162 81 ^ (13 * 82) <
      explicitFiniteFiberPrimeThreshold 1411732827 := by
  apply
    free_finite_fiber_energy_coefficient_lt_prime_threshold (a := 82) (B := 1411717327) (u :=
      1411732827) (c := 162) (h := 81)
  · exact freeFiniteFiberCountCoefficient_162_81_lt_double_exp (by norm_num only)
  · norm_num only

/-- The precision-280, loss-140 count coefficient supports energy exponent
105 at the explicit prime threshold `P(4,217,312,731)`. -/
theorem free_finite_fiber_energy_coefficient_lt_prime_threshold_280_140_105 :
    (2 ^ 176 : ℕ) ^ 105 * freeFiniteFiberCountCoefficient 280 140 ^ (13 * 105) <
      explicitFiniteFiberPrimeThreshold 4217312731 := by
  apply
    free_finite_fiber_energy_coefficient_lt_prime_threshold (a := 105) (B := 4217292884) (u :=
      4217312731) (c := 280) (h := 140)
  · exact freeFiniteFiberCountCoefficient_280_140_lt_double_exp (by norm_num only)
  · norm_num only

/-- The precision-168, loss-84 count coefficient supports energy exponent
210 below the prime threshold P(1,518,265,178). -/
theorem free_finite_fiber_energy_coefficient_lt_prime_threshold_168_84_210 :
    (2 ^ 176 : ℕ) ^ 210 * freeFiniteFiberCountCoefficient 168 84 ^ (13 * 210) <
      explicitFiniteFiberPrimeThreshold 1518265178 := by
  apply
    free_finite_fiber_energy_coefficient_lt_prime_threshold (a := 210) (B := 1518225486) (u :=
      1518265178) (c := 168) (h := 84)
  · exact freeFiniteFiberCountCoefficient_168_84_lt_double_exp (by norm_num only)
  · norm_num only

/-- The precision-164, loss-82 coefficient supports the squared energy
exponent 2,240 below the explicit prime threshold `P(1,447,213,072)`. -/
theorem free_finite_fiber_energy_coefficient_lt_prime_threshold_164_82_2240 :
    (2 ^ 176 : ℕ) ^ 2240 * freeFiniteFiberCountCoefficient 164 82 ^ (13 * 2240) <
      explicitFiniteFiberPrimeThreshold 1447213072 := by
  apply
    free_finite_fiber_energy_coefficient_lt_prime_threshold (a := 2240) (B := 1446789710) (u :=
      1447213072) (c := 164) (h := 82)
  · exact freeFiniteFiberCountCoefficient_164_82_lt_double_exp (by norm_num only)
  · norm_num only

/-- Cast the free complete-count coefficient to the real harmonic constant
`4K(1 + 1/(1/h/2))`. Expanding reciprocals identifies that factor with
`2h+1` exactly. -/
theorem freeFiniteFiberCountCoefficient_cast (c h : ℕ) :
    (freeFiniteFiberCountCoefficient c h : ℝ) =
      4 * (eightDegreeFreeFiberCoefficient c : ℝ) * (1 + 1 / ((1 / (h : ℝ)) / 2)) := by
  rw [one_div_div, div_div_eq_mul_div, div_one]
  simp only [freeFiniteFiberCountCoefficient, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one]
  ring

/-- With precision `1/c ≤ eta`, the alternative eight-degree coefficient
controls every restricted ratio by `K T p^(1/84+eta)`. Absorb the height
power using `T ≤ p` and monotonicity in the prime exponent. -/
theorem heightRestrictedRatioSet_le_explicit_free_finite_fiber_ratio_bound {eta : ℝ} {c : ℕ}
    (hc : 0 < c) (hprec : 1 / (c : ℝ) ≤ eta) :
    ∀ (p H T : ℕ) [Fact p.Prime],
      H < p →
        (T : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ) →
        ((heightRestrictedRatioSet p H T).card : ℝ) ≤
          eightDegreeFreeFiberCoefficient c * T * (p : ℝ) ^ (1 / 84 + eta) := by
  let K : ℝ := eightDegreeFreeFiberCoefficient c
  have hK : 0 < K := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hbound := heightRestrictedRatioSet_le_explicit_free_eight_degree_bound hc
  intro p H T hp hHp htop
  have hp1 : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (Fact.out : p.Prime).pos
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hTp : (T : ℝ) ≤ p :=
    htop.trans
      (by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num only : (5 / 28 : ℝ) ≤ 1))
  have hpow : (T : ℝ) ^ (1 / (c : ℝ)) ≤ (p : ℝ) ^ eta :=
    (Real.rpow_le_rpow (Nat.cast_nonneg T) hTp
          (div_nonneg (by norm_num only) (Nat.cast_nonneg c))).trans
      (Real.rpow_le_rpow_of_exponent_le hp1 hprec)
  have hsplit : (T : ℝ) ^ (1 + 1 / (c : ℝ)) = T * (T : ℝ) ^ (1 / (c : ℝ)) := by
    rw [Real.rpow_add_of_nonneg (Nat.cast_nonneg T) (by norm_num only : (0 : ℝ) ≤ 1)
        (div_nonneg (by norm_num only) (Nat.cast_nonneg c)),
      Real.rpow_one]
  have hh := hbound p H T hHp htop
  rw [hsplit] at hh
  have hm :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (mul_nonneg hK.le (Nat.cast_nonneg T)))
      (Real.rpow_nonneg (Nat.cast_nonneg p) (1 / 84))
  have hm' :
    K * T * (T : ℝ) ^ (1 / (c : ℝ)) * (p : ℝ) ^ (1 / 84 : ℝ) ≤
      K * T * (p : ℝ) ^ (1 / 84 + eta) := by
    rw [Real.rpow_add hp0]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
  apply LE.le.trans _ hm'
  simpa only [mul_assoc] using hh

/-- Separate the count-loss parameter `h` from the height precision `c`.
Under `1/c ≤ (1/h)/2`, every odd prime and admissible height has the stated
full congruence-count bound. The reciprocal-height sum uses half of `1/h`
for its logarithmic factor, leaving the other half in the prime exponent. -/
theorem boundedCongruenceCount_le_explicit_free_finite_fiber {h c : ℕ} (hh : 0 < h) (hc : 0 < c)
    (hprec : 1 / (c : ℝ) ≤ (1 / (h : ℝ)) / 2) :
    ∀ (p H : ℕ) [Fact p.Prime],
      Odd p →
        H < p →
        (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ) →
        (boundedCongruenceCount p H : ℝ) ≤
          freeFiniteFiberCountCoefficient c h * H * (p : ℝ) ^ (1 / 84 + 1 / (h : ℝ)) := by
  let eta : ℝ := 1 / (h : ℝ)
  have heta : 0 < eta := div_pos (by norm_num only) (Nat.cast_pos.mpr hh)
  have hdelta : 0 < eta / 2 := half_pos heta
  let K : ℝ := eightDegreeFreeFiberCoefficient c
  have hK : 0 < K := Nat.cast_pos.mpr (Nat.succ_pos _)
  let C : ℝ := 4 * K * (1 + 1 / (eta / 2))
  intro p H hp hodd hHp htop
  rw [freeFiniteFiberCountCoefficient_cast]
  change (boundedCongruenceCount p H : ℝ) ≤ C * H * (p : ℝ) ^ (1 / 84 + eta)
  have hR :=
    heightRestrictedRatioSet_le_explicit_free_finite_fiber_ratio_bound (eta := eta / 2) hc hprec
  have hp1 : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (Fact.out : p.Prime).pos
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hcount :=
    boundedCongruenceCount_le_of_uniform_height_ratios hodd hHp hK.le
      (fun T hT ↦ hR p H T hHp ((Nat.cast_le.mpr hT).trans htop))
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg H) (Nat.cast_le.mpr hHp.le) hdelta.le
  have hlog :=
    (Real.log_natCast_le_rpow_div H hdelta).trans (div_le_div_of_nonneg_right hpow hdelta.le)
  have hone : (1 : ℝ) ≤ (p : ℝ) ^ (eta / 2) := by
    have h := Real.rpow_le_rpow_of_exponent_le hp1 hdelta.le
    simpa only [Real.rpow_zero] using h
  have hlog' : 1 + Real.log H ≤ (1 + 1 / (eta / 2)) * (p : ℝ) ^ (eta / 2) := by
    have hh := add_le_add hone hlog
    convert hh using 1
    ring
  have hm :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog'
        (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hK.le) (Nat.cast_nonneg H)))
      (Real.rpow_nonneg hp0.le (1 / 84 + eta / 2))
  apply hcount.trans
  convert hm using 1
  dsimp only [C]
  rw [show (1 / 84 + eta : ℝ) = eta / 2 + (1 / 84 + eta / 2) by ring, Real.rpow_add hp0]
  ring

/-- Raise the free-precision full count bound to an independent energy power
`a`, then absorb its prime exponent into the requested integer `g`. This
connects the independent count-loss and finite-band parameters to energy
estimates without imposing `h = a`. -/
theorem boundedCongruenceCount_power_le_explicit_free_finite_fiber {a h c g : ℕ} (ha : 0 < a)
    (hh : 0 < h) (hc : 0 < c) (hprec : 1 / (c : ℝ) ≤ (1 / (h : ℝ)) / 2)
    (hratio : 1 / 84 + 1 / (h : ℝ) ≤ (g : ℝ) / a) :
    ∀ (p H : ℕ) [Fact p.Prime],
      Odd p →
        H < p →
        (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ) →
        boundedCongruenceCount p H ^ a ≤
          freeFiniteFiberCountCoefficient c h ^ a * H ^ a * p ^ g := by
  intro p H hp hodd hHp htop
  have hcount := boundedCongruenceCount_le_explicit_free_finite_fiber hh hc hprec p H hodd hHp htop
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hp1 : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (Fact.out : p.Prime).pos
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (boundedCongruenceCount p H)) hcount a
  have hratioPow := Real.rpow_le_rpow_of_exponent_le hp1 hratio
  have hpid : ((p : ℝ) ^ ((g : ℝ) / a)) ^ a = (p : ℝ) ^ g := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p),
      div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (ne_of_gt ha)), Real.rpow_natCast]
  have hprime : ((p : ℝ) ^ (1 / 84 + 1 / (h : ℝ))) ^ a ≤ (p : ℝ) ^ g := by
    calc
      _ ≤ ((p : ℝ) ^ ((g : ℝ) / a)) ^ a := pow_le_pow_left₀ (Real.rpow_nonneg hp0 _) hratioPow a
      _ = _ := hpid
  rw [mul_pow, mul_pow] at hpow
  have hfactor :
    (freeFiniteFiberCountCoefficient c h : ℝ) ^ a * (H : ℝ) ^ a *
        ((p : ℝ) ^ (1 / 84 + 1 / (h : ℝ))) ^ a ≤
      (freeFiniteFiberCountCoefficient c h : ℝ) ^ a * (H : ℝ) ^ a * (p : ℝ) ^ g :=
    mul_le_mul_of_nonneg_left hprime
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Nat.cast_nonneg _) _))
  apply Nat.cast_le (α := ℝ).mp
  simpa only [Nat.cast_mul, Nat.cast_pow] using hpow.trans hfactor

end PseudoPrime.NumberTheory.Heilbronn
