/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerMomentIntegral
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerPrefixAt

/-! # An explicit lower bound for the Euler increment -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The explicit lower bound for one of the first three Euler moments above
1000. The retained boundary correction and the finite integral are both exact. -/
noncomputable def quarterEulerMomentLower (k : ℕ) (b : ℝ) : ℝ :=
  -((1000 : ℝ) ^ (3 / 4 : ℝ)) *
      AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k 1000 +
    quarterEulerMomentIntegral k b

/-- Under RH, combining the first three moment bounds gives a lower bound for
the Euler increment on `(1000,b]`. The coefficients are those of the kernel weight. -/
theorem quarter_euler_increment_lower (hRH : RiemannHypothesis) {b : ℝ} (hb : (1000 : ℝ) ≤ b) :
    (3 / 8 : ℝ) * quarterEulerMomentLower 0 b + (81 / 200 : ℝ) * quarterEulerMomentLower 1 b +
        (729 / 5000 : ℝ) * quarterEulerMomentLower 2 b ≤
      ∑ n ∈ Finset.Ioc 1000 ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have h0 := quarter_euler_moment_lower hRH (k := 0) (by decide) hb
  have h1 := quarter_euler_moment_lower hRH (k := 1) (by decide) hb
  have h2 := quarter_euler_moment_lower hRH (k := 2) (by decide) hb
  rw [quarter_euler_moment_integral_eq 0 hb] at h0
  rw [quarter_euler_moment_integral_eq 1 hb] at h1
  rw [quarter_euler_moment_integral_eq 2 hb] at h2
  norm_num only [Nat.floor_ofNat] at h0 h1 h2
  change quarterEulerMomentLower 0 b ≤ _ at h0
  change quarterEulerMomentLower 1 b ≤ _ at h1
  change quarterEulerMomentLower 2 b ≤ _ at h2
  have he :
    (∑ n ∈ Finset.Ioc 1000 ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) =
      (3 / 8 : ℝ) * (∑ n ∈ Finset.Ioc 1000 ⌊b⌋₊, quarterMangoldtMoment 0 n) +
        (81 / 200 : ℝ) * (∑ n ∈ Finset.Ioc 1000 ⌊b⌋₊, quarterMangoldtMoment 1 n) +
        (729 / 5000 : ℝ) * (∑ n ∈ Finset.Ioc 1000 ⌊b⌋₊, quarterMangoldtMoment 2 n) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [quarterMangoldtMoment, refinedSixEulerWeight]
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
    simp only [pow_zero, pow_one]
    ring
  rw [he]
  linarith only [h0, h1, h2]

/-- The certified 1000-prefix and the analytic increment bound combine into
a lower Euler prefix at every real cutoff at least 1000. -/
theorem quarter_euler_prefix_from_increment (hRH : RiemannHypothesis) {b : ℝ}
    (hb : (1000 : ℝ) ≤ b) :
    (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5 + (3 / 8 : ℝ) * quarterEulerMomentLower 0 b +
        (81 / 200 : ℝ) * quarterEulerMomentLower 1 b +
        (729 / 5000 : ℝ) * quarterEulerMomentLower 2 b ≤
      ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have hp := refined_euler_prefix_1000_at (X := 1000) (by norm_num only)
  norm_num only [Nat.floor_ofNat] at hp
  have ht := quarter_euler_increment_lower hRH hb
  have hfloor : 1000 ≤ ⌊b⌋₊ := Nat.le_floor hb
  have hsplit :=
    Finset.sum_Ioc_consecutive
      (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n)
      (show 0 ≤ 1000 by decide) hfloor
  linarith only [hp, ht, hsplit]

end PseudoPrime.PrimeTestBounds.MillerRabin
