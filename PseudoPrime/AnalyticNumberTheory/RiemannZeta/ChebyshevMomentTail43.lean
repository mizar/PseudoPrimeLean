/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevMoment43
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogMomentLimit

/-! # Infinite Mangoldt moment tails under the Chebyshev envelope -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH and the stated Rosser-type count estimate, limits of the finite
Chebyshev lower and upper Abel expressions bound the infinite von Mangoldt
moment tail for `σ > 1`. The two envelope limits are explicit hypotheses;
the arithmetic convergence follows from the proved moment summability. -/
theorem mangoldt_tail_bounds_43 (hRH : RiemannHypothesis) {σ a A B : ℝ} (k : ℕ) (ha : 0 < a)
    (hL : 43 ≤ Real.log a) (hσ : 1 < σ) (hk : (k : ℝ) ≤ σ * Real.log a)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t))
    (hlo :
      Filter.Tendsto
        (fun n : ℕ ↦
          Arithmetic.mangoldtMomentWeight σ k n * chebyshevMinorant43 n -
            Arithmetic.mangoldtMomentWeight σ k a * Chebyshev.psi a -
            ∫ t in Set.Ioc a (n : ℝ),
              Arithmetic.mangoldtMomentWeightDeriv σ k t * chebyshevMinorant43 t)
        Filter.atTop (nhds A))
    (hhi :
      Filter.Tendsto
        (fun n : ℕ ↦
          Arithmetic.mangoldtMomentWeight σ k n * chebyshevMajorant43 n -
            Arithmetic.mangoldtMomentWeight σ k a * Chebyshev.psi a -
            ∫ t in Set.Ioc a (n : ℝ),
              Arithmetic.mangoldtMomentWeightDeriv σ k t * chebyshevMajorant43 t)
        Filter.atTop (nhds B)) :
    A ≤
        (∑' m : ℕ, Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m) -
          (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
            Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m) ∧
      (∑' m : ℕ, Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m) -
          (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
            Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m) ≤
        B := by
  have htail := Arithmetic.tendsto_mangoldt_moment_tail hσ k a
  have hn :=
    (tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop).eventually
      (Filter.eventually_ge_atTop a)
  constructor
  · apply le_of_tendsto_of_tendsto hlo htail
    filter_upwards [hn] with n hn
    simpa only [Nat.floor_natCast] using
      (mangoldt_tail_lower_43 hRH k ha hL hn (le_of_lt (zero_lt_one.trans hσ)) hk hQ)
  · apply le_of_tendsto_of_tendsto htail hhi
    filter_upwards [hn] with n hn
    simpa only [Nat.floor_natCast] using
      (mangoldt_tail_upper_43 hRH k ha hL hn (le_of_lt (zero_lt_one.trans hσ)) hk hQ)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
