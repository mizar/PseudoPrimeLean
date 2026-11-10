/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentVariableTail
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerInfiniteTail

/-! Euler tail decomposition into three Mangoldt moment tails. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The refined Euler tail is the positive linear combination of the first three Mangoldt moment
tails. The finite identity extends to infinity by the established tail limits. -/
theorem quarter_euler_tail_moment_eq (a : ℝ) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) -
        (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) =
      (3 / 8 : ℝ) *
          ((∑' n : ℕ, quarterMangoldtMoment 0 n) -
            ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, quarterMangoldtMoment 0 n) +
        (81 / 200 : ℝ) *
          ((∑' n : ℕ, quarterMangoldtMoment 1 n) -
            ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, quarterMangoldtMoment 1 n) +
        (729 / 5000 : ℝ) *
          ((∑' n : ℕ, quarterMangoldtMoment 2 n) -
            ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, quarterMangoldtMoment 2 n) := by
  have h0 := (quarter_moment_tendsto_from 0 ⌊a⌋₊).const_mul (3 / 8 : ℝ)
  have h1 := (quarter_moment_tendsto_from 1 ⌊a⌋₊).const_mul (81 / 200 : ℝ)
  have h2 := (quarter_moment_tendsto_from 2 ⌊a⌋₊).const_mul (729 / 5000 : ℝ)
  have h := (h0.add h1).add h2
  have he (N : ℕ) :
    (3 / 8 : ℝ) * (∑ n ∈ Finset.Ioc ⌊a⌋₊ N, quarterMangoldtMoment 0 n) +
        (81 / 200 : ℝ) * (∑ n ∈ Finset.Ioc ⌊a⌋₊ N, quarterMangoldtMoment 1 n) +
        (729 / 5000 : ℝ) * (∑ n ∈ Finset.Ioc ⌊a⌋₊ N, quarterMangoldtMoment 2 n) =
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ N, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [quarterMangoldtMoment, refinedSixEulerWeight]
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
    simp only [pow_zero, pow_one]
    ring
  have h' := h.congr (fun N ↦ he N)
  exact tendsto_nhds_unique (refined_euler_tail_tendsto a) h'

/-- The Chebyshev-envelope bound for one Euler moment tail at cutoff `a`. It consists of the
cutoff correction and the nonnegative envelope-derivative integral. -/
noncomputable def quarterMomentTailCap (k : ℕ) (a : ℝ) : ℝ :=
  AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k a *
      (a + a ^ (3 / 4 : ℝ) - Chebyshev.psi a) +
    ∫ t in Set.Ioi a, quarterMomentTailIntegrand k t

/-- Under RH, the refined Euler tail above any real cutoff at least 625 is at most the positive
combination of the three quarter-power Chebyshev-envelope moment bounds. -/
theorem quarter_euler_tail_moment_upper (hRH : RiemannHypothesis) {a : ℝ} (ha : 625 ≤ a) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) -
        (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) ≤
      (3 / 8 : ℝ) * quarterMomentTailCap 0 a + (81 / 200 : ℝ) * quarterMomentTailCap 1 a +
        (729 / 5000 : ℝ) * quarterMomentTailCap 2 a := by
  have he : Real.exp (2 : ℝ) < 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num only, Real.exp_add]
    nlinarith only [Real.exp_one_lt_d9, Real.exp_pos 1, sq_nonneg (Real.exp 1 - (29 / 10 : ℝ))]
  have hlog (t : ℝ) (ht : a ≤ t) : (2 : ℝ) ≤ Real.log t := by
    have ht0 : 0 < t := by linarith only [ha, ht]
    exact (Real.le_log_iff_exp_le ht0).mpr (by linarith only [ha, ht, he])
  have h0 :=
    quarter_moment_infinite_from hRH 0 ha
      (fun t ht ↦ by
        have h := hlog t ht
        norm_num only
        linarith only [h])
  have h1 :=
    quarter_moment_infinite_from hRH 1 ha
      (fun t ht ↦ by
        have h := hlog t ht
        norm_num only
        linarith only [h])
  have h2 :=
    quarter_moment_infinite_from hRH 2 ha
      (fun t ht ↦ by
        have h := hlog t ht
        norm_num only
        linarith only [h])
  rw [quarter_euler_tail_moment_eq]
  dsimp only [quarterMomentTailCap]
  linarith only [h0, h1, h2]

/-- The Chebyshev cutoff correction is at most twice the three-quarter-power error. Under RH,
this removes the unknown psi value from a nonnegative Euler moment envelope. -/
theorem quarter_moment_tail_cap_le (hRH : RiemannHypothesis) (k : ℕ) {a : ℝ} (ha : 625 ≤ a) :
    quarterMomentTailCap k a ≤
      2 * AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k a * a ^ (3 / 4 : ℝ) +
        ∫ t in Set.Ioi a, quarterMomentTailIntegrand k t := by
  have ha1 : 1 ≤ a := by linarith only [ha]
  have hpsi := (abs_le.mp (quarter_psi_error_rpow hRH ha)).1
  have hw : 0 ≤ AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k a := by
    dsimp only [AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight]
    exact
      mul_nonneg (Real.rpow_nonneg (zero_le_one.trans ha1) _) (pow_nonneg (Real.log_nonneg ha1) k)
  have h :=
    mul_le_mul_of_nonneg_left
      (show a + a ^ (3 / 4 : ℝ) - Chebyshev.psi a ≤ 2 * a ^ (3 / 4 : ℝ) by linarith only [hpsi]) hw
  dsimp only [quarterMomentTailCap]
  linarith only [h]

/-- The explicit moment-tail envelope without a Chebyshev psi term. It consists of twice the
cutoff weight times the quarter-power error and the envelope-derivative integral. -/
noncomputable def quarterMomentCleanTail (k : ℕ) (a : ℝ) : ℝ :=
  2 * AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k a * a ^ (3 / 4 : ℝ) +
    ∫ t in Set.Ioi a, quarterMomentTailIntegrand k t

/-- Under RH, the refined Euler tail at every real cutoff at least 625 is bounded without any
remaining Chebyshev psi term, using three explicit moment envelopes. -/
theorem quarter_euler_tail_clean_upper (hRH : RiemannHypothesis) {a : ℝ} (ha : 625 ≤ a) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) -
        (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) ≤
      (3 / 8 : ℝ) * quarterMomentCleanTail 0 a + (81 / 200 : ℝ) * quarterMomentCleanTail 1 a +
        (729 / 5000 : ℝ) * quarterMomentCleanTail 2 a := by
  have h := quarter_euler_tail_moment_upper hRH ha
  have h0 := quarter_moment_tail_cap_le hRH 0 ha
  have h1 := quarter_moment_tail_cap_le hRH 1 ha
  have h2 := quarter_moment_tail_cap_le hRH 2 ha
  dsimp only [quarterMomentCleanTail]
  linarith only [h, h0, h1, h2]

end PseudoPrime.PrimeTestBounds.MillerRabin
