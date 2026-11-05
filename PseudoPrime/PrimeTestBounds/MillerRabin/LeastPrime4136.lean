/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GlobalMax4136
public import PseudoPrime.PrimeTestBounds.MillerRabin.LogNineComparison

/-! # Least rejecting prime bounds at coefficient 0.4136 and base nine -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the least prime rejecting an odd composite `n > 1` is bounded by
`max 2 ((517/1250) * (log n)²)`. Leastness transfers the global actual-witness bound
to `compositeLeastPrime`, the project representation of `q_MR(n)`. -/
theorem compositeLeastPrime_le_max_4136 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (compositeLeastPrime n : ℝ) ≤ max 2 ((517 / 1250 : ℝ) * (Real.log n) ^ 2) := by
  obtain ⟨r, hr, hb, hf⟩ := exists_prime_reject_max_4136 hn ho hc hGRH
  have hleast := (compositeLeastPrime_spec hGRH hn ho hc).2.2 r hr hf
  exact (Nat.cast_le.mpr hleast).trans hb

/-- Under GRH, `q_MR(n)` is at most `2 * (logb 9 n)²` for every odd composite `n > 1`.
Such an input is at least nine, so the max-form comparison converts the least-prime bound
to the base-nine logarithm without a separate small-input hypothesis. -/
theorem compositeLeastPrime_le_log9_sq {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (compositeLeastPrime n : ℝ) ≤ 2 * (Real.logb 9 n) ^ 2 := by
  have hn9 : 9 ≤ n := by
    by_contra h9
    have hp : ∀ k : Fin 9, 1 < k.val → Odd k.val → k.val.Prime := by decide +kernel
    exact hc (hp ⟨n, Nat.lt_of_not_ge h9⟩ hn ho)
  exact
    (compositeLeastPrime_le_max_4136 hn ho hc hGRH).trans
      (max_04136_le_logb_nine_sq (Nat.cast_le.mpr hn9))

/-- Under GRH, every odd composite `n > 1` has an actual rejecting prime at most
`2 * (logb 9 n)²`. Use the specified least rejecting prime and its base-nine bound. -/
theorem exists_prime_reject_le_log9_sq {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ 2 * (Real.logb 9 n) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hspec := compositeLeastPrime_spec hGRH hn ho hc
  exact ⟨compositeLeastPrime n, hspec.1, compositeLeastPrime_le_log9_sq hn ho hc hGRH, hspec.2.1⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
