/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt
import PseudoPrime.AnalyticNumberTheory.Arithmetic.AlternatingSums
import Mathlib.Tactic

/-! # General bounds and arithmetic certificates -/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Every exponent in the logarithmic cutoff places `2` in the corresponding
prime cutoff whenever `x ≥ 2`. -/
theorem two_mem_prime_cutoff_of_two_le {x : ℝ} (hx : 2 ≤ x) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊) : 2 ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ := by
  have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hquot_nonneg : 0 ≤ Real.log x / Real.log 2 := by
    exact div_nonneg (Real.log_nonneg (by linarith)) hlog2.le
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
      ⟨by norm_num only, (Nat.le_floor_iff (Real.rpow_nonneg (by linarith) _)).mpr hrpow⟩

/-!
The odd reciprocal tail is a geometric progression.  Keeping this finite-sum
interface local makes the `χ̃(2) = -1` correction bound independent of the
cutoff used by the analytic consumer.
-/

/-- The odd inverse powers of `2` have total mass at most `2 / 3`. -/
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
      · omega
      · exact ⟨j, by omega⟩
    · intro j₁ hj₁ j₂ hj₂ h
      omega
    · intro k hk
      simp only [s, Finset.mem_filter, Finset.mem_Icc] at hk
      rcases hk.2 with ⟨j, rfl⟩
      refine ⟨j, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
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
  nlinarith

end PseudoPrime.AnalyticNumberTheory.Arithmetic
