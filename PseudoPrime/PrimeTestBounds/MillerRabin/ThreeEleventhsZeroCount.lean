/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountConjugation
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTail
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevSquareLog
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountErrorNumerics
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTailAnchored
import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeEleventhsConditional
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenCumulative
import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeElevenths10300
import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeElevenths4M
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterNonuniformLog8
import PseudoPrime.PrimeTestBounds.MillerRabin.LeastRejectingPrime

/-! # Three-elevenths bound from an explicit zero-count estimate -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a logarithmic zero-count error through height 522230 and the
stated inverse-square tail bounds between heights 1250 and 522230 imply the
maximum three-elevenths least-witness bound for every odd composite. The two
zero inputs are explicit and cover only the needed heights. -/
theorem three_eleven_least_of_finite_count {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hQ :
      ∀ t ∈ Set.Icc (2 * Real.pi * Real.exp 1) (522230 : ℝ),
        |AnalyticNumberTheory.RiemannZeta.positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t)
    (hTail :
      ∀ T ∈ Set.Icc (1250 : ℝ) 522230,
        AnalyticNumberTheory.RiemannZeta.ordinateTail T ≤ Real.log T / (Real.pi * T)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  apply three_eleven_least_on_psi4m hn ho hc hGRH
  intro x hlo hhi
  have hbase : (25000000 : ℝ) ≤ ((52223 / 100000 : ℝ) * 10300) ^ 2 := by norm_num only
  have hx : (25000000 : ℝ) ≤ x := hbase.trans hlo
  have hslo : (5000 : ℝ) ≤ Real.sqrt x := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hx]
  have hshi : Real.sqrt x ≤ (2088920 : ℝ) := by
    apply (Real.sqrt_le_left (by norm_num only)).2
    norm_num only at hhi ⊢
    exact hhi
  have hTlo : (1250 : ℝ) ≤ Real.sqrt x / 4 := by linarith only [hslo]
  have hThi : Real.sqrt x / 4 ≤ (522230 : ℝ) := by linarith only [hshi]
  apply AnalyticNumberTheory.RiemannZeta.psi_lower_square_tail hGRH.riemann hx
  · intro t ht
    exact hQ t ⟨ht.1, ht.2.trans hThi⟩
  · exact hTail (Real.sqrt x / 4) ⟨hTlo, hThi⟩

/-- Under GRH, the displayed zero-count estimate through height 522230 and
one inverse-square tail bound at that height imply the maximum
three-elevenths least-witness bound. Finite Abel summation supplies all lower
tail cutoffs. Both zero inputs remain explicit hypotheses. -/
theorem three_eleven_least_of_count_anchor {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hQ :
      ∀ t ∈ Set.Icc (2 * Real.pi * Real.exp 1) (522230 : ℝ),
        |AnalyticNumberTheory.RiemannZeta.positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t)
    (hAnchor :
      AnalyticNumberTheory.RiemannZeta.ordinateTail 522230 ≤
        (1 / Real.pi) * (Real.log 522230 - Real.log (2 * Real.pi) + 1) / 522230 +
          1 / (522230 : ℝ) ^ 2) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  apply three_eleven_least_of_finite_count hn ho hc hGRH hQ
  intro T hT
  apply
    AnalyticNumberTheory.RiemannZeta.ordinateTail_of_finite_count hGRH.riemann
      (by linarith only [hT.1]) hT.2 ?_ hAnchor
  intro t ht
  apply hQ t
  constructor
  · have hbase : 2 * Real.pi * Real.exp 1 ≤ T := by
      have hp :=
        mul_le_mul Real.pi_lt_four.le Real.exp_one_lt_three.le (Real.exp_pos 1).le
          (by norm_num only : (0 : ℝ) ≤ 4)
      nlinarith only [hp, hT.1]
    exact hbase.trans ht.1
  · exact ht.2

/-- Under GRH and a positive-height zero-count error at most `log t`, the
least rejecting prime of every odd composite satisfies the maximum
three-elevenths bound. The coarse zero-count estimate is an extra hypothesis. -/
theorem three_eleven_least_of_coarse_count {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |AnalyticNumberTheory.RiemannZeta.positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  by_cases h10300 : Real.log n ≤ 10300
  · exact three_eleven_least_to10300 hn ho hc hGRH h10300
  have hL : (10300 : ℝ) ≤ Real.log n := le_of_not_ge h10300
  have hbound :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    by_cases hu : UniformKorseltTriple n
    · by_cases hU : Real.log n ≤ 4000000
      · exact uniform_three_eleven_count_to4m hn ho hu hGRH hQ hU
      · exact three_eleven_from_4m hn ho hc hGRH (le_of_not_ge hU)
    · obtain ⟨p, hp, hb, hf⟩ := quarter_nonuniform_log8 hn ho hc hu hGRH (by linarith only [hL])
      have hcoef : (1 / 4 : ℝ) ≤ 3 / 11 := by norm_num only
      exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  obtain ⟨p, hp, hb, hf⟩ := hbound
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject ⟨p, hp, hb.trans (le_max_right _ _), hf⟩

/-- Under GRH and the stated Rosser-type positive-height zero-count estimate,
the least rejecting prime of every odd composite is bounded by the maximum
of 2 and three elevenths of its squared logarithm. The explicit zero count is
an additional hypothesis; the Chebyshev input follows from it. -/
theorem three_eleven_least_of_count {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |AnalyticNumberTheory.RiemannZeta.positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  apply three_eleven_least_of_coarse_count hn ho hc hGRH
  intro t ht
  exact (hQ t ht).trans (AnalyticNumberTheory.RiemannZeta.rosser_error_le_log ht)

end PseudoPrime.PrimeTestBounds.MillerRabin
