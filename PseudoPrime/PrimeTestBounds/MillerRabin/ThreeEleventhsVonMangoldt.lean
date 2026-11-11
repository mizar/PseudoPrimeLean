/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundGammaCellPrimitive
public import PseudoPrime.PrimeTestBounds.MillerRabin.LeastPrimeCumulative

/-! # Three-elevenths bound from the normalized zero-count identity -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH and the Euler-normalized Riemann–von Mangoldt identity, every
odd composite has a least rejecting prime within the `3/11` cutoff. The
Gamma integral identity and the classification are proved internally. -/
theorem three_eleven_least_of_rvm {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hV : EulerRiemannVonMangoldt) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  exact three_eleven_least_of_gamma_complex hn ho hc hGRH hV backlund_gamma_complex_identity

/-- Under GRH and the Euler-normalized Riemann–von Mangoldt identity, the
least prime rejecting an odd composite satisfies the `3/11` bound. The
leastness specification transfers the proved witness bound to the function. -/
theorem composite_least_prime_three_eleven {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hV : EulerRiemannVonMangoldt) :
    (compositeLeastPrime n : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) := by
  obtain ⟨p, hp, hb, hf, _⟩ := three_eleven_least_of_rvm hn ho hc hGRH hV
  have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hf
  exact (Nat.cast_le.mpr hm).trans hb

end PseudoPrime.PrimeTestBounds.MillerRabin
