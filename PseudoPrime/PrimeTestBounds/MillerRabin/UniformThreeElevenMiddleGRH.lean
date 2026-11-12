/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenMiddle
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevSquareLowerRH

/-! # Uniform middle interval under GRH -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple with `10300 ≤ log n ≤ 4000000`
has a rejecting prime at most `(3/11) * log n ^ 2`. The proved RH zero-count
estimate supplies the analytic input of the middle-interval theorem. -/
theorem uniform_three_eleven_middle_grh {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (10300 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 4000000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let r : ℝ := (52223 / 100000 : ℝ) * Real.log n
  have hrL : (52223 / 100000 : ℝ) * 10300 ≤ r := by
    dsimp only [r]
    exact mul_le_mul_of_nonneg_left hL (by norm_num only)
  have hr0 : 0 ≤ r := le_trans (by norm_num only) hrL
  have hXlo : ((52223 / 100000 : ℝ) * 10300) ^ 2 ≤ r ^ 2 :=
    pow_le_pow_left₀ (by norm_num only) hrL 2
  have hbase : (25000000 : ℝ) ≤ ((52223 / 100000 : ℝ) * 10300) ^ 2 := by norm_num only
  have hp :=
    AnalyticNumberTheory.RiemannZeta.psi_lower_square_twelve_of_RH hGRH.riemann (hbase.trans hXlo)
  rw [Real.sqrt_sq hr0] at hp
  exact uniform_three_eleven_middle_at hn ho hu hGRH hp hL hU

end PseudoPrime.PrimeTestBounds.MillerRabin
