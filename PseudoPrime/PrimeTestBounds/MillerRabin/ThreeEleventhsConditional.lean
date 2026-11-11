/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeElevenths10300
import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeElevenths4M
import PseudoPrime.PrimeTestBounds.MillerRabin.LeastRejectingPrime
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterNonuniformLog8
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenCumulative

/-! # Conditional three-elevenths bound on the full range -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the displayed Chebyshev lower bound on the finite interval of
radii between logarithmic scales 10300 and four million gives a rejecting
prime within the maximum three-elevenths cutoff for every odd composite. -/
theorem three_eleven_max_on_psi4m {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hpsi :
      ∀ x : ℝ,
        ((52223 / 100000 : ℝ) * 10300) ^ 2 ≤ x →
          x ≤ ((52223 / 100000 : ℝ) * 4000000) ^ 2 →
          x - (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.psi x) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h10300 : Real.log n ≤ 10300
  · obtain ⟨p, hp, hb, hf, _⟩ := three_eleven_least_to10300 hn ho hc hGRH h10300
    exact ⟨p, hp, hb, hf⟩
  have hL : (10300 : ℝ) ≤ Real.log n := le_of_not_ge h10300
  have hcoef : (1 / 4 : ℝ) ≤ 3 / 11 := by norm_num only
  have hbound :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    by_cases hbig : (4000000 : ℝ) ≤ Real.log n
    · exact three_eleven_from_4m hn ho hc hGRH hbig
    have hU : Real.log n ≤ 4000000 := le_of_not_ge hbig
    by_cases hu : UniformKorseltTriple n
    · exact uniform_three_eleven_to4m hn ho hu hGRH hpsi hU
    · obtain ⟨p, hp, hb, hf⟩ := quarter_nonuniform_log8 hn ho hc hu hGRH (by linarith only [hL])
      exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  obtain ⟨p, hp, hb, hf⟩ := hbound
  exact ⟨p, hp, hb.trans (le_max_right _ _), hf⟩

/-- Under GRH and the displayed Chebyshev lower bound on the finite range of
radii needed by the uniform middle intervals, every odd composite has a
rejecting prime within the maximum three-elevenths cutoff. -/
theorem three_eleven_max_on_psi {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hpsi :
      ∀ x : ℝ,
        ((52223 / 100000 : ℝ) * 10300) ^ 2 ≤ x →
          x ≤ ((52223 / 100000 : ℝ) * 5000000) ^ 2 →
          x - (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.psi x) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply three_eleven_max_on_psi4m hn ho hc hGRH
  intro x hlo hhi
  apply hpsi x hlo
  have hbounds : ((52223 / 100000 : ℝ) * 4000000) ^ 2 ≤ ((52223 / 100000 : ℝ) * 5000000) ^ 2 := by
    norm_num only
  exact hhi.trans hbounds

/-- Under GRH and the displayed log-square Chebyshev lower bound above one
million, every odd composite admits a rejecting prime within the maximum
three-elevenths cutoff. The unconditional small and high ranges surround the
conditional uniform middle intervals. -/
theorem three_eleven_max_of_psi {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hpsi :
      ∀ x : ℝ, 1000000 ≤ x → x - (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.psi x) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply three_eleven_max_on_psi hn ho hc hGRH
  intro x hlo hhi
  apply hpsi x
  have hbase : (1000000 : ℝ) ≤ ((52223 / 100000 : ℝ) * 10300) ^ 2 := by norm_num only
  exact hbase.trans hlo

/-- Under GRH and the displayed Chebyshev lower bound on the radii between
logarithmic scales 10300 and four million, the least rejecting prime satisfies
the maximum three-elevenths bound. The minimum is extracted from the witness. -/
theorem three_eleven_least_on_psi4m {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hpsi :
      ∀ x : ℝ,
        ((52223 / 100000 : ℝ) * 10300) ^ 2 ≤ x →
          x ≤ ((52223 / 100000 : ℝ) * 4000000) ^ 2 →
          x - (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.psi x) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject (three_eleven_max_on_psi4m hn ho hc hGRH hpsi)

/-- Under GRH and the displayed finite-range Chebyshev lower bound, the least
rejecting prime of every odd composite satisfies the maximum three-elevenths
cutoff. Extract the minimum from the finite-range conditional witness. -/
theorem three_eleven_least_on_psi {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hpsi :
      ∀ x : ℝ,
        ((52223 / 100000 : ℝ) * 10300) ^ 2 ≤ x →
          x ≤ ((52223 / 100000 : ℝ) * 5000000) ^ 2 →
          x - (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.psi x) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject (three_eleven_max_on_psi hn ho hc hGRH hpsi)

/-- Under GRH and the displayed Chebyshev lower bound, the least rejecting
prime of any odd composite satisfies the maximum three-elevenths cutoff. The
least witness is extracted from the conditional full-range witness bound. -/
theorem three_eleven_least_of_psi {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hpsi :
      ∀ x : ℝ, 1000000 ≤ x → x - (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.psi x) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject (three_eleven_max_of_psi hn ho hc hGRH hpsi)

end PseudoPrime.PrimeTestBounds.MillerRabin
