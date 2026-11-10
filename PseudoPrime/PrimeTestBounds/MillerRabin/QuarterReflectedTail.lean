/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedMoments
public import PseudoPrime.LLS.ChebyshevQuarterError
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogMomentAbel
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTailPsi

/-! # Finite reflected moment tails under RH -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The logarithm at the arithmetic cutoff exceeds four. A rational
logarithm certificate supplies the fixed margin used for all six degrees. -/
theorem quarter_log2701_lower : (4 : ℝ) ≤ Real.log 2701 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 2701 12 32 4 8 = true from by decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at h
  exact h

/-- Under RH, every finite tail of the first six reflected Mangoldt moments
is bounded by the Chebyshev `t + t^(3/4)` envelope. The lower boundary term
at 2701 remains explicit for the limiting tail calculation. -/
theorem quarter_moment_tail_finite (hRH : RiemannHypothesis) {k : ℕ} (hk : k < 6) {b : ℝ}
    (hb : (2701 : ℝ) ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊(2701 : ℝ)⌋₊ ⌊b⌋₊, quarterMangoldtMoment k n) ≤
      AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k b *
          (b + Real.sqrt b * Real.sqrt (Real.sqrt b)) -
        AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k 2701 * Chebyshev.psi 2701 -
        ∫ t in Set.Ioc (2701 : ℝ) b,
          AnalyticNumberTheory.Arithmetic.mangoldtMomentWeightDeriv (79 / 50) k t *
            (t + Real.sqrt t * Real.sqrt (Real.sqrt t)) := by
  let E : ℝ → ℝ := fun t ↦ t + Real.sqrt t * Real.sqrt (Real.sqrt t)
  have hE : ContinuousOn E (Set.Icc 2701 b) := by
    dsimp only [E]
    fun_prop
  have hψ : ∀ t ∈ Set.Icc (2701 : ℝ) b, Chebyshev.psi t ≤ E t := by
    intro t ht
    have h :=
      (abs_le.mp (LLS.psi_error_quarter_sqrt hRH (show (625 : ℝ) ≤ t by linarith only [ht.1]))).2
    dsimp only [E]
    linarith only [h]
  have hd :
    ∀ t ∈ Set.Icc (2701 : ℝ) b,
      AnalyticNumberTheory.Arithmetic.mangoldtMomentWeightDeriv (79 / 50) k t ≤ 0 := by
    intro t ht
    have hlog := Real.log_le_log (show (0 : ℝ) < 2701 by norm_num only) ht.1
    have hk' : (k : ℝ) ≤ 5 := by exact_mod_cast (Nat.le_of_lt_succ hk)
    apply
      AnalyticNumberTheory.Arithmetic.mangoldt_moment_deriv_nonpos k (by norm_num only)
        (by linarith only [ht.1])
    nlinarith only [quarter_log2701_lower, hlog, hk']
  have h :=
    AnalyticNumberTheory.Arithmetic.mangoldt_moment_tail_upper (79 / 50) k
      (show (1 : ℝ) ≤ 2701 by norm_num only) hb E hE hψ hd
  dsimp only [E] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [quarterMangoldtMoment, AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight]
  ring

/-- On the nonnegative half-line, the product of the first two repeated
square roots equals the real three-quarter power. -/
theorem quarter_sqrt_product {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt t * Real.sqrt (Real.sqrt t) = t ^ (3 / 4 : ℝ) := by
  by_cases hz : t = 0
  · simp only [hz, Real.sqrt_zero, mul_zero, Real.zero_rpow (by norm_num only : (3 / 4 : ℝ) ≠ 0)]
  · have ht0 : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ht, ← Real.rpow_add ht0]
    norm_num only

/-- The finite moment tail under RH after cancellation of the upper
Chebyshev boundary. The remaining integral has the two power-logarithm terms
that occur in the paper's infinite-tail formula. -/
theorem quarter_moment_tail_integral (hRH : RiemannHypothesis) {k : ℕ} (hk : k < 6) {b : ℝ}
    (hb : (2701 : ℝ) ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊(2701 : ℝ)⌋₊ ⌊b⌋₊, quarterMangoldtMoment k n) ≤
      AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k 2701 *
          (2701 + (2701 : ℝ) ^ (3 / 4 : ℝ) - Chebyshev.psi 2701) +
        ∫ t in Set.Ioc (2701 : ℝ) b,
          (1 + (3 / 4 : ℝ) * t ^ (-(1 / 4 : ℝ))) *
            AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k t := by
  have hk' : (k : ℝ) ≤ 5 := by exact_mod_cast (Nat.le_of_lt_succ hk)
  have hlog (t : ℝ) (ht : t ∈ Set.Icc (2701 : ℝ) b) : (k : ℝ) ≤ (79 / 50 : ℝ) * Real.log t := by
    have h := Real.log_le_log (show (0 : ℝ) < 2701 by norm_num only) ht.1
    nlinarith only [quarter_log2701_lower, h, hk']
  have h :=
    quarter_moment_tail_envelope hRH (79 / 50) k (a := (2701 : ℝ)) (b := b) (by norm_num only) hb
      (by norm_num only) hlog
  convert h using 1
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [quarterMangoldtMoment, AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
