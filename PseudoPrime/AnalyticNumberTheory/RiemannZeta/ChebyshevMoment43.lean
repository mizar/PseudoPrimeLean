/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPrimePowers
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogMomentAbel
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogMomentLowerFinite

/-! # Logarithmic Mangoldt moments from the Chebyshev envelope -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Chebyshev majorant `x + sqrt x log x (log x - log log x)/(8π)`.
On logarithmic scales at least 43 it bounds `ψ` under RH and the stated
Rosser-type zero-count hypothesis, and it is used in finite Abel summation. -/
noncomputable def chebyshevMajorant43 (x : ℝ) : ℝ :=
  x + Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi))

/-- The Chebyshev minorant `x - sqrt x log x (log x - log log x)/(8π)`.
Under RH and the stated Rosser-type count hypothesis it bounds `ψ` below
on logarithmic scales at least 43 and supplies finite lower Abel bounds. -/
noncomputable def chebyshevMinorant43 (x : ℝ) : ℝ :=
  x - Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi))

/-- Under RH and the stated Rosser-type zero-count hypothesis, both `ψ` and
`θ` satisfy the same square-root logarithmic envelope when `log x ≥ 43`.
Drop the proved positive margin from the stronger estimates. -/
theorem chebyshev_errors_43 (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) (hL : 43 ≤ Real.log x)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    |Chebyshev.psi x - x| ≤
        Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) ∧
      |Chebyshev.theta x - x| ≤
        Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  have hp := psi_error_envelope_of_log hRH hx hL hQ
  have ht := theta_error_envelope_of_log hRH hx hL hQ
  have hs := Real.sqrt_nonneg x
  constructor
  · nlinarith only [hp, hs]
  · nlinarith only [ht, hs]

/-- Under RH and the stated Rosser-type count estimate, bound a finite
power-logarithm von Mangoldt moment tail above by Abel summation against the
Chebyshev majorant. The logarithmic scale is at least 43 throughout the
interval, and the weight decreases once `σ log a ≥ k`. -/
theorem mangoldt_tail_upper_43 (hRH : RiemannHypothesis) {σ a b : ℝ} (k : ℕ) (ha : 0 < a)
    (hL : 43 ≤ Real.log a) (hab : a ≤ b) (hσ : 0 ≤ σ) (hk : (k : ℝ) ≤ σ * Real.log a)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        Arithmetic.mangoldtMomentWeight σ k n * ArithmeticFunction.vonMangoldt n) ≤
      Arithmetic.mangoldtMomentWeight σ k b * chebyshevMajorant43 b -
        Arithmetic.mangoldtMomentWeight σ k a * Chebyshev.psi a -
        ∫ t in Set.Ioc a b, Arithmetic.mangoldtMomentWeightDeriv σ k t * chebyshevMajorant43 t := by
  have ha1 : 1 ≤ a := (Real.log_pos_iff ha.le).mp (by linarith only [hL]) |>.le
  apply Arithmetic.mangoldt_moment_tail_upper σ k ha1 hab chebyshevMajorant43
  · intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    have hlog := Real.log_le_log ha ht.1
    have hl := Real.continuousAt_log ht0.ne'
    have hl0 : Real.log t ≠ 0 := ne_of_gt (by linarith only [hL, hlog])
    have hll := (Real.continuousAt_log hl0).comp hl
    exact
      (continuousAt_id.add
          (Real.continuous_sqrt.continuousAt.mul
            ((hl.mul (hl.sub hll)).div_const (8 * Real.pi)))).continuousWithinAt
  · intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    have hlog := Real.log_le_log ha ht.1
    have hp := psi_error_envelope_of_log hRH ht0 (by linarith only [hL, hlog]) hQ
    have hs := Real.sqrt_nonneg t
    have hu := (abs_le.mp hp).2
    dsimp only [chebyshevMajorant43]
    nlinarith only [hu, hs]
  · intro t ht
    have ht1 : 1 ≤ t := ha1.trans ht.1
    have hlog := Real.log_le_log ha ht.1
    have hm := mul_le_mul_of_nonneg_left hlog hσ
    exact Arithmetic.mangoldt_moment_deriv_nonpos k hσ ht1 (hk.trans hm)

/-- Under RH and the stated Rosser-type count estimate, bound a finite
power-logarithm von Mangoldt moment tail below by Abel summation against the
Chebyshev minorant. The weight decreases once `σ log a ≥ k`, and the actual
lower boundary is retained. -/
theorem mangoldt_tail_lower_43 (hRH : RiemannHypothesis) {σ a b : ℝ} (k : ℕ) (ha : 0 < a)
    (hL : 43 ≤ Real.log a) (hab : a ≤ b) (hσ : 0 ≤ σ) (hk : (k : ℝ) ≤ σ * Real.log a)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    Arithmetic.mangoldtMomentWeight σ k b * chebyshevMinorant43 b -
        Arithmetic.mangoldtMomentWeight σ k a * Chebyshev.psi a -
        ∫ t in Set.Ioc a b, Arithmetic.mangoldtMomentWeightDeriv σ k t * chebyshevMinorant43 t ≤
      (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        Arithmetic.mangoldtMomentWeight σ k n * ArithmeticFunction.vonMangoldt n) := by
  have ha1 : 1 ≤ a := (Real.log_pos_iff ha.le).mp (by linarith only [hL]) |>.le
  apply Arithmetic.mangoldt_moment_tail_lower σ k ha1 hab chebyshevMinorant43
  · intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    have hlog := Real.log_le_log ha ht.1
    have hl := Real.continuousAt_log ht0.ne'
    have hl0 : Real.log t ≠ 0 := ne_of_gt (by linarith only [hL, hlog])
    have hll := (Real.continuousAt_log hl0).comp hl
    exact
      (continuousAt_id.sub
          (Real.continuous_sqrt.continuousAt.mul
            ((hl.mul (hl.sub hll)).div_const (8 * Real.pi)))).continuousWithinAt
  · intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    have hlog := Real.log_le_log ha ht.1
    have hp := psi_error_envelope_of_log hRH ht0 (by linarith only [hL, hlog]) hQ
    have hs := Real.sqrt_nonneg t
    have hu := (abs_le.mp hp).1
    dsimp only [chebyshevMinorant43]
    nlinarith only [hu, hs]
  · intro t ht
    have ht1 : 1 ≤ t := ha1.trans ht.1
    have hlog := Real.log_le_log ha ht.1
    have hm := mul_le_mul_of_nonneg_left hlog hσ
    exact Arithmetic.mangoldt_moment_deriv_nonpos k hσ ht1 (hk.trans hm)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
