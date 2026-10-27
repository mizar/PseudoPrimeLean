/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FullEndpointPolynomial
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReciprocalGapFullEndpoint

/-! # Gap-free MR witnesses from endpoint limits and polynomial positivity -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For odd composite N>1 under GRH and 64<=Y<=x, negativity of the full endpoint
limit gives a prime rejecting the canonical strong test at most x. Extract a
positive gap and apply the single original-level separation theorem.
Neither a gap choice nor any finite arithmetic support is required. -/
theorem exists_prime_reject_of_fullEndpointLimit_neg {N : ℕ} [NeZero N] (hn : 1 < N) (ho : Odd N)
    (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y : ℝ}
    (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hlim : LLS.PaperStatements.reciprocalGapFullEndpointLimit N x Y < 0) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ x ∧ (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  obtain ⟨h, hh, hs⟩ := LLS.PaperStatements.exists_pos_gap_of_fullEndpointLimit_neg N hx.le hlim
  exact exists_prime_reject_of_full_endpoint_separation hn ho hc hGRH hh hx hY hYx hs

/-- For odd composite N>1 under GRH and y>=8, positivity of the rational-pi
endpoint polynomial at L=log N,z=log y gives a rejecting prime at most y^2.
Use equal squared cutoffs, the exact polynomial identity and the right-limit
witness theorem. This reduces the analytic bound to one real polynomial sign. -/
theorem exists_prime_reject_of_fullEndpointPolynomial_pos {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {y : ℝ} (hy : 8 ≤ y)
    (hpoly :
      0 < LLS.PaperStatements.fullEndpointPolynomial (Real.log N) (2096 / 1831) y (Real.log y)) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ y ^ 2 ∧
        (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  have hy1 : 1 < y := lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 8) hy
  have hx : 1 < y ^ 2 := by nlinarith only [hy]
  have hY : (64 : ℝ) ≤ y ^ 2 := by nlinarith only [hy]
  exact
    exists_prime_reject_of_fullEndpointLimit_neg hn ho hc hGRH hx hY (le_refl _)
      (LLS.PaperStatements.fullEndpointLimit_neg_of_rational_polynomial_pos N hy1 hpoly)

end PseudoPrime.PrimeTestBounds.MillerRabin
