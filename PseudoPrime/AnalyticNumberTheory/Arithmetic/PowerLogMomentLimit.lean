/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogMomentAbel
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

/-- For a summable real series whose zeroth term vanishes, tails beginning
strictly above a fixed real cutoff converge to the total sum minus its finite
prefix. Both finite intervals retain their upper endpoints. -/
theorem tendsto_tail_prefix (f : ℕ → ℝ) (hf0 : f 0 = 0) (hf : Summable f) (a : ℝ) :
    Filter.Tendsto (fun n : ℕ ↦ ∑ m ∈ Finset.Ioc ⌊a⌋₊ n, f m) Filter.atTop
      (nhds ((∑' m : ℕ, f m) - ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, f m)) := by
  have ht := hf.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have ht' :
    Filter.Tendsto (fun n : ℕ ↦ ∑ m ∈ Finset.Ioc 0 n, f m) Filter.atTop (nhds (∑' m : ℕ, f m)) := by
    apply Filter.Tendsto.congr (fun n ↦ ?_) ht
    dsimp only [Function.comp_apply]
    rw [Nat.range_eq_Icc_zero_sub_one (n + 1) (Nat.add_one_ne_zero n), Nat.add_sub_cancel, ←
      Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le n)]
    simp only [hf0, add_zero]
  have hm := ht'.sub_const (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, f m)
  apply Filter.Tendsto.congr' ?_ hm
  apply (Filter.eventually_ge_atTop ⌊a⌋₊).mono
  intro n hn
  have hd : Disjoint (Finset.Ioc 0 ⌊a⌋₊) (Finset.Ioc ⌊a⌋₊ n) :=
    Finset.disjoint_left.mpr
      (fun m hm ht ↦ (not_lt_of_ge (Finset.mem_Ioc.mp hm).2) (Finset.mem_Ioc.mp ht).1)
  have he := Finset.sum_union (f := f) hd
  rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hn] at he
  dsimp only
  linarith only [he]

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
