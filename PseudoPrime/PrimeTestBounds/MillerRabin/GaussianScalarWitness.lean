/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPairGap
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDeficitCertified

/-! # Actual Gaussian witness from a scalar comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an explicit scalar comparison gives a rejecting prime for a
squarefree uniform Korselt triple through the Gaussian cutoff. The certified
principal deficit and actual three-character gap discharge all analytic moment
hypotheses; only the displayed scalar comparison remains to be verified. -/
theorem exists_prime_reject_of_gaussian_scalar {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q]
    [NeZero r] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)]
    [Fact (2 < r)] (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {x h : ℝ} (hx : 1 ≤ x) (hh : 0 < h)
    (hh1 : h ≤ 1 / 32) (hX : 50000 ≤ (21 / 10 : ℝ) * x)
    (hscore :
      (20115621 / 25000000 : ℝ) * Real.log n + 683 / 50 - 108 / 25 - 4 * (1129059 / 200000 : ℝ) +
          (1536 / 27 : ℝ) / x +
          (2129 / 2000 : ℝ) * (((7 / 3 : ℝ) * Real.log n + 12) / Real.sqrt x) +
          (1419 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) ≤
        4 *
            (Real.sqrt x * (81470555 / 100000000 : ℝ) -
              (7 / 50 : ℝ) / Real.sqrt x *
                ((32 / 63 : ℝ) * h * ((21 / 10 : ℝ) * x) +
                  (231 / 2500 : ℝ) * (Real.sqrt ((21 / 10 : ℝ) * x) + 1) / h +
                  1839 / 1000) -
              ((231 / 5000 : ℝ) * Real.sqrt ((21 / 10 : ℝ) * x) +
                  (1839 / 1000 : ℝ) * Real.log ((21 / 10 : ℝ) * x) +
                  2) /
                Real.sqrt x) -
          (Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13)) :
    ∃ l : ℕ,
      l.Prime ∧ (l : ℝ) ≤ (21 / 10 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hX0 : 0 ≤ (21 / 10 : ℝ) * x := by linarith only [hX]
  have hX1 : 1 ≤ (21 / 10 : ℝ) * x := by linarith only [hX]
  let s : Finset ℕ := Finset.Ioc 0 ⌊(21 / 10 : ℝ) * x⌋₊
  have hs : ∀ k ∈ s, (k : ℝ) ≤ (21 / 10 : ℝ) * x := by
    intro k hk
    exact (Nat.cast_le.mpr (Finset.mem_Ioc.mp hk).2).trans (Nat.floor_le hX0)
  have hdef := gaussian_deficit_certified hGRH.riemann hx0 hX1 hh hh1
  have hgap := hscore.trans hdef
  exact
    exists_prime_reject_of_gaussian_gap hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn
      hpK hqK hrK hvq hvr hx s hs hX hgap

end PseudoPrime.PrimeTestBounds.MillerRabin
