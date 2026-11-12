/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogMomentAbel
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.NaturalTailLimit
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogBoundarySummation
import PseudoPrime.Analysis.LogarithmicPowerAbsorption

/-! # Infinite tails of power-logarithm Mangoldt moments -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For `σ > 1`, a von Mangoldt series with any fixed logarithmic moment is
summable. Absorb the logarithmic power into half the available power saving
and compare with the existing summable Mangoldt Dirichlet series. -/
theorem summable_mangoldt_moment {σ : ℝ} (hσ : 1 < σ) (k : ℕ) :
    Summable (fun n : ℕ ↦ mangoldtMomentWeight σ k n * ArithmeticFunction.vonMangoldt n) := by
  let ε : ℝ := (σ - 1) / 2
  let τ : ℝ := (σ + 1) / 2
  have hε : 0 < ε := by
    dsimp only [ε]; linarith only [hσ]
  have hτ : 1 < τ := by
    dsimp only [τ]; linarith only [hσ]
  have hsum := summable_powerMangoldtWeight hτ
  apply Summable.of_norm_bounded_eventually hsum
  rw [Nat.cofinite_eq_atTop]
  have hsmall :=
    Analysis.eventually_mul_one_add_log_pow_lt_rpow (C := 1) (s := ε) (by norm_num only) hε k
  have hnat :=
    (tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop).eventually
      hsmall
  filter_upwards [hnat, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hp := pow_le_pow_left₀ hnlog (show Real.log (n : ℝ) ≤ 1 + Real.log n by linarith only) k
  have hlogpow : Real.log (n : ℝ) ^ k ≤ (n : ℝ) ^ ε := by
    simp only [one_mul] at hn
    exact hp.trans hn.le
  have hpow := mul_le_mul_of_nonneg_left hlogpow (Real.rpow_nonneg hn0.le (-σ))
  have heq : (n : ℝ) ^ (-σ) * (n : ℝ) ^ ε = (n : ℝ) ^ (-τ) := by
    rw [← Real.rpow_add hn0]
    congr 1
    dsimp only [ε, τ]
    ring
  rw [heq] at hpow
  have hm := mul_le_mul_of_nonneg_right hpow (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  have hnonneg : 0 ≤ mangoldtMomentWeight σ k n * ArithmeticFunction.vonMangoldt n :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hn0.le _) (pow_nonneg hnlog k))
      ArithmeticFunction.vonMangoldt_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  dsimp only [mangoldtMomentWeight]
  nlinarith only [hm]

/-- For `σ > 1`, finite von Mangoldt moment tails converge to the complete
series minus the prefix through the lower cutoff. The open lower endpoint is
preserved, so this is the limit required by the finite Abel estimates. -/
theorem tendsto_mangoldt_moment_tail {σ : ℝ} (hσ : 1 < σ) (k : ℕ) (a : ℝ) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ∑ m ∈ Finset.Ioc ⌊a⌋₊ n, mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m)
      Filter.atTop
      (nhds
        ((∑' m : ℕ, mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m) -
          ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
            mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m)) := by
  apply tendsto_tail_prefix _ ?_ (summable_mangoldt_moment hσ k) a
  simp only [ArithmeticFunction.map_zero, mul_zero]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
