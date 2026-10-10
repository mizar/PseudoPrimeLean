/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.AlternatingSums
public import Mathlib.Tactic

/-! # General bounds and arithmetic certificates -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- If `x ≥ 2` and `1 ≤ k ≤ floor (log x / log 2)`, then two belongs to the natural
cutoff `Ioc 0 (floor (x^(1/k)))`. The logarithmic bound gives `2^k ≤ x`, and monotonicity
of positive real powers gives `2 ≤ x^(1/k)`. This ensures the prime two is present in
each relevant prime-power sum used in the two-adic correction. -/
theorem two_mem_prime_cutoff_of_two_le {x : ℝ} (hx : 2 ≤ x) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊) : 2 ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ := by
  have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hquot_nonneg : 0 ≤ Real.log x / Real.log 2 := by
    exact div_nonneg (Real.log_nonneg (by linarith only [hx])) hlog2.le
  have hklog : (k : ℝ) ≤ Real.log x / Real.log 2 :=
    (Nat.le_floor_iff hquot_nonneg).mp (Finset.mem_Icc.mp hk).2
  have hlog : (k : ℝ) * Real.log 2 ≤ Real.log x := (le_div_iff₀ hlog2).mp hklog
  have hpow : (2 : ℝ) ^ k ≤ x := by
    have h :=
      Real.rpow_le_of_le_log (x := (2 : ℝ) ^ k) (y := x) (z := (1 : ℝ)) hxpos
        (by simpa only [Real.log_pow, one_mul] using hlog)
    simpa only [ge_iff_le, Real.rpow_one] using h
  have hrpow : (2 : ℝ) ≤ x ^ ((1 : ℝ) / k) := by
    have h :=
      (Real.le_rpow_inv_iff_of_pos (x := (2 : ℝ)) (y := x) (z := (k : ℝ)) (by norm_num only)
            hxpos.le (by exact_mod_cast hkpos)).2
        (by simpa only [Real.rpow_natCast] using hpow)
    simpa only [one_div, ge_iff_le] using h
  exact
    Finset.mem_Ioc.mpr
      ⟨by norm_num only, (Nat.le_floor_iff (Real.rpow_nonneg (by linarith only [hx]) _)).mpr hrpow⟩

/-!
The odd reciprocal tail is a geometric progression.  Keeping this finite-sum
interface local makes the `χ̃(2) = -1` correction bound independent of the
cutoff used by the analytic consumer.
-/

/-- For any natural cutoff `K`, the sum of `2^(-k)` over odd `k` in `Icc 1 K` is at most
`2/3`. Reindexing odd exponents as `2*j + 1` gives a finite geometric sum with initial
term `1/2` and ratio `1/4`. This bounds odd-exponent corrections independently of the cutoff. -/
theorem sum_odd_inv_two_pow_le (K : ℕ) :
    ∑ k ∈ Finset.Icc (1 : ℕ) K, (if Odd k then (1 : ℝ) / (2 : ℝ) ^ k else 0) ≤ 2 / 3 := by
  classical
  let s : Finset ℕ := (Finset.Icc 1 K).filter Odd
  have hs :
    ∑ k ∈ Finset.Icc (1 : ℕ) K, (if Odd k then (1 : ℝ) / (2 : ℝ) ^ k else 0) =
      ∑ k ∈ s, (1 : ℝ) / (2 : ℝ) ^ k := by
    rw [show s = (Finset.Icc (1 : ℕ) K).filter Odd by rfl]
    symm
    exact Finset.sum_filter Odd (fun k => (1 : ℝ) / (2 : ℝ) ^ k)
  have hgeom :
    (∑ k ∈ s, (1 : ℝ) / (2 : ℝ) ^ k) =
      ∑ j ∈ Finset.range ((K + 1) / 2), (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ j := by
    symm
    apply Finset.sum_bij (fun j _ => 2 * j + 1)
    · intro j hj
      simp only [Finset.mem_range] at hj
      simp only [s, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · constructor
        · exact Nat.succ_le_succ (Nat.zero_le (2 * j))
        · clear * - hj
          have hmul : j * 2 < (K + 1) - (2 - 1) :=
            (Nat.lt_div_iff_mul_lt (by norm_num only : 0 < 2)).mp hj
          have hmul' : j * 2 < K := by simpa only [Nat.add_sub_cancel] using hmul
          have hbound : j * 2 + 1 ≤ K := Nat.succ_le_of_lt hmul'
          simpa only [Nat.mul_comm j 2] using hbound
      · exact ⟨j, rfl⟩
    · intro j₁ hj₁ j₂ hj₂ h
      clear * - h
      have hmul : 2 * j₁ = 2 * j₂ := Nat.add_right_cancel h
      exact Nat.mul_left_cancel (by norm_num only : 0 < 2) hmul
    · intro k hk
      simp only [s, Finset.mem_filter, Finset.mem_Icc] at hk
      rcases hk.2 with ⟨j, rfl⟩
      refine ⟨j, ?_, ?_⟩
      · simp only [Finset.mem_range]
        clear * - hk
        apply (Nat.lt_div_iff_mul_lt (by norm_num only : 0 < 2)).2
        have hlt : 2 * j < K := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hk.1.2
        simpa only [Nat.mul_comm j 2, Nat.add_sub_cancel] using hlt
      · rfl
    · intro j hj
      simp only [Finset.mem_range] at hj
      rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num only]
      rw [← pow_mul]
      rw [← one_div_pow]
      rw [mul_comm, ← pow_succ]
  rw [hs, hgeom, Finset.range_eq_Ico, ← Finset.mul_sum]
  have h :=
    geom_sum_Ico_le_of_lt_one (x := (1 / 4 : ℝ)) (m := 0) (n := (K + 1) / 2) (by norm_num only)
      (by norm_num only)
  nlinarith only [h]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
