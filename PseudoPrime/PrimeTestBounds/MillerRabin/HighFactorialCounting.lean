/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Combinatorics.LogFactorialBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.HighPrimeSupply99

/-! # Factorial-based prime-product counting at high scale -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The logarithm of `197 / 200` is at least `-1 / 50`. A rational interval certificate supplies
the positive margin needed when the factorial bound replaces paired-factor counting. -/
theorem log_factorial_base_197 : (-1 / 50 : ℝ) ≤ Real.log (197 / 200 : ℝ) := by
  have hc : Analysis.rationalLogIntervalCheck (197 / 200) 0 12 (-1 / 50) 1 = true := by
    decide +kernel
  have h := (Analysis.rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] at h
  linarith only [h]

/-- The `99 / 100` supply ratio yields a logarithmic binomial lower bound with coefficient
`49 / 50` and the explicit loss `log (k + 1)`. The factorial estimate retains the loss needed
for a rigorous variable-radius counting budget. -/
theorem log_choose_of_supply_99 {L α b u : ℝ} {M k : ℕ} (hL : 70000 ≤ L) (hα : (647 / 1000 : ℝ) ≤ α)
    (hb : α * L - 1 ≤ b) (hu0 : 0 < u) (hu : u ≤ L / 2000) (hkM : k ≤ M)
    (hM : ((99 / 100 : ℝ) * b ^ 2) / u < (M : ℝ) + 1) (hk : (k : ℝ) < α * L / u)
    (hlog : u = 2 * Real.log b) :
    (k : ℝ) * (u / 2 + 49 / 50) - Real.log ((k : ℝ) + 1) ≤ Real.log (Nat.choose M k : ℝ) := by
  have hαL : (647 / 1000 : ℝ) * L ≤ α * L := mul_le_mul_of_nonneg_right hα (by linarith only [hL])
  have hb0 : 0 < b := by linarith only [hL, hαL, hb]
  have hratio := high_paired_ratio_99 hL hα hb hu0 hu hkM hM hk
  rw [mul_div_assoc] at hratio
  have hrat : (197 / 200 : ℝ) * b < ((M + 1 - k : ℕ) : ℝ) / (k + 1) := by linarith only [hratio]
  have hpos : 0 < (197 / 200 : ℝ) * b := mul_pos (by norm_num only) hb0
  have hlogR := Real.log_lt_log hpos hrat
  rw [Real.log_mul (by norm_num only : (197 / 200 : ℝ) ≠ 0) hb0.ne'] at hlogR
  have hbound : u / 2 + (49 / 50 : ℝ) ≤ Real.log (((M + 1 - k : ℕ) : ℝ) / (k + 1)) + 1 := by
    linarith only [hlog, hlogR, log_factorial_base_197]
  have hmul := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg k)
  have hchoose := Combinatorics.log_choose_lower hkM
  linarith only [hmul, hchoose]

/-- The factorial counting budget exceeds the cofactor logarithm when the scalar gap is at
least `3 / 200`, the quadratic error is at most `L / 70`, and `log (k + 1) ≤ u`. The positive
remaining margin absorbs both the ceiling and factorial losses. -/
theorem factorial_budget_of_gap {L α u U : ℝ} {k : ℕ} (hL : 0 < L) (hu : 0 < u) (huU : u ≤ U)
    (hα : α ≤ 2 / 3) (hgap : (3 / 2 * α - 1) * U + (49 / 50) * α ≥ 3 / 200)
    (hm : (3 / 2 : ℝ) * u ^ 2 + (49 / 50) * u ≤ L / 70) (hk : α * L / u - 1 ≤ (k : ℝ))
    (hlogk : Real.log ((k : ℝ) + 1) ≤ u) :
    (1 - α) * L < (k : ℝ) * (u / 2 + 49 / 50) - Real.log ((k : ℝ) + 1) := by
  have hbase : 0 ≤ u / 2 + (49 / 50 : ℝ) := by linarith only [hu]
  have hgapU : 0 ≤ (1 - (3 / 2 : ℝ) * α) * (U - u) :=
    mul_nonneg (by linarith only [hα]) (by linarith only [huU])
  have hgap' : (3 / 200 : ℝ) ≤ ((3 / 2 : ℝ) * α - 1) * u + (49 / 50) * α := by
    nlinarith only [hgap, hgapU]
  have hgapL := mul_le_mul_of_nonneg_left hgap' hL.le
  have hbudget' : (1 - α) * L * u < (α * L - u) * (u / 2 + 49 / 50) - u ^ 2 := by
    nlinarith only [hgapL, hm, hL]
  have hk' : α * L - u ≤ (k : ℝ) * u := by
    have hh := (sub_le_iff_le_add).mp hk
    have hh' := (div_le_iff₀ hu).mp hh
    nlinarith only [hh']
  have hmulk := mul_le_mul_of_nonneg_right hk' hbase
  have hlogmul := mul_le_mul_of_nonneg_right hlogk hu.le
  have hc : (1 - α) * L * u < ((k : ℝ) * (u / 2 + 49 / 50) - Real.log ((k : ℝ) + 1)) * u := by
    nlinarith only [hbudget', hmulk, hlogmul]
  exact lt_of_mul_lt_mul_right hc hu.le

/-- The `99 / 100` supply and the factorial scalar gap produce a binomial count exceeding the
large-cofactor kernel budget. The logarithm of `k + 1` is retained in the budget rather than
discarded. -/
theorem factorial_count_of_gap {L α b u U : ℝ} {M k : ℕ} (hL : 70000 ≤ L)
    (hα : (647 / 1000 : ℝ) ≤ α) (hα2 : α ≤ 2 / 3) (hb : α * L - 1 ≤ b) (hu0 : 0 < u)
    (hu : u ≤ L / 2000) (huU : u ≤ U) (hkM : k ≤ M)
    (hM : ((99 / 100 : ℝ) * b ^ 2) / u < (M : ℝ) + 1) (hklo : α * L / u - 1 ≤ (k : ℝ))
    (hkhi : (k : ℝ) < α * L / u) (hlog : u = 2 * Real.log b) (hlogk : Real.log ((k : ℝ) + 1) ≤ u)
    (hgap : (3 / 2 * α - 1) * U + (49 / 50) * α ≥ 3 / 200)
    (hm : (3 / 2 : ℝ) * u ^ 2 + (49 / 50) * u ≤ L / 70) :
    Real.exp ((1 - α) * L) < (Nat.choose M k : ℝ) := by
  have hbudget := factorial_budget_of_gap (by linarith only [hL]) hu0 huU hα2 hgap hm hklo hlogk
  have hcount := log_choose_of_supply_99 hL hα hb hu0 hu hkM hM hkhi hlog
  have he := Real.exp_lt_exp.mpr (hbudget.trans_le hcount)
  rw [Real.exp_log (Nat.cast_pos.mpr (Nat.choose_pos hkM))] at he
  exact he

end PseudoPrime.PrimeTestBounds.MillerRabin
