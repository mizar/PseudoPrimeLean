/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Global

/-! # Cumulative three-tenths bound for least rejecting primes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every input at most `N` has its total least-prime value bounded
by the global maximum cutoff at `N`. For target inputs, monotonicity of the
logarithm transfers the witness bound; all other inputs contribute zero. -/
theorem compositeLeastPrime_le_03_upper
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n N : ℕ} (hnN : n ≤ N) :
    (compositeLeastPrime n : ℝ) ≤ max 2 ((3 / 10 : ℝ) * Real.log N ^ 2) := by
  by_cases hn : 1 < n ∧ Odd n ∧ ¬n.Prime
  · have hl0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn.1.le)
    have hlog := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn.1)) (Nat.cast_le.mpr hnN)
    have hs := (sq_le_sq₀ hl0 (hl0.trans hlog)).mpr hlog
    obtain ⟨p, hp, hb, hr⟩ := exists_prime_reject_03_global hn.1 hn.2.1 hn.2.2 hGRH
    have hm := (compositeLeastPrime_spec hGRH hn.1 hn.2.1 hn.2.2).2.2 p hp hr
    exact
      ((Nat.cast_le.mpr hm).trans hb).trans
        (max_le_max (le_refl _) (mul_le_mul_of_nonneg_left hs (by norm_num only)))
  · rw [compositeLeastPrime, ite_eq_right hn, Nat.cast_zero]
    exact (by norm_num only : (0 : ℝ) ≤ 2).trans (le_max_left _ _)

/-- Under GRH, the cumulative maximum of least rejecting primes through `N`
is bounded by the global maximum cutoff at `N`. Take the finite supremum of
the preceding pointwise bound. -/
theorem cumulativeLeastPrime_le_03 (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (N : ℕ) : (cumulativeLeastPrime N : ℝ) ≤ max 2 ((3 / 10 : ℝ) * Real.log N ^ 2) := by
  have h0 : (0 : ℝ) ≤ max 2 ((3 / 10 : ℝ) * Real.log N ^ 2) :=
    (by norm_num only : (0 : ℝ) ≤ 2).trans (le_max_left _ _)
  have hb : cumulativeLeastPrime N ≤ ⌊max 2 ((3 / 10 : ℝ) * Real.log N ^ 2)⌋₊ := by
    apply Finset.sup_le
    intro n hn
    apply Nat.le_floor
    exact compositeLeastPrime_le_03_upper hGRH (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
  exact (Nat.cast_le.mpr hb).trans (Nat.floor_le h0)

end PseudoPrime.PrimeTestBounds.MillerRabin
