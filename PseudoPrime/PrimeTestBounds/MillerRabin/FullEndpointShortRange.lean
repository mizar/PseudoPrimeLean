/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FullEndpointShortRange
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointPolynomial

/-! # Analytic MR witness bound with correction twenty-two fifths on 8<=log N<=16 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For an odd composite N>1 under GRH with 8<=log N<=16, a rejecting prime
exists below (log N-2*log log N+22/5)^2. Apply the polynomial witness criterion to
the continuous correction-4.4 positivity theorem. No finite modulus verification
or selected prime-power table is used. -/
theorem exists_prime_reject_le_fourPointFourRoot_sq {N : ℕ} [NeZero N] (hn : 1 < N) (ho : Odd N)
    (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL8 : 8 ≤ Real.log N) (hL16 : Real.log N ≤ 16) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Real.log N - 2 * Real.log (Real.log N) + 22 / 5) ^ 2 ∧
        (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  have hy := (LLS.PaperStatements.fullEndpoint_fourPointFour_root_data hL8 hL16).1
  exact
    exists_prime_reject_of_fullEndpointPolynomial_pos hn ho hc hGRH hy
      (LLS.PaperStatements.fullEndpoint_polynomial_pos_for_fourPointFour hL8 hL16)

/-- Under the same GRH and logarithmic interval conditions, if log log N>11/5,
one rejecting prime satisfies both the correction-4.4 bound and strict log-square
bound. Use the radius comparison for the already obtained witness.
The two estimates concern the same prime, without any minimum formula. -/
theorem exists_prime_reject_le_fourPointFourRoot_sq_and_lt_log_sq {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL8 : 8 ≤ Real.log N) (hL16 : Real.log N ≤ 16) (hu : 11 / 5 < Real.log (Real.log N)) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Real.log N - 2 * Real.log (Real.log N) + 22 / 5) ^ 2 ∧
        (p : ℝ) < (Real.log N) ^ 2 ∧
        (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  obtain ⟨p, hp, hpx, hpow, hall⟩ :=
    exists_prime_reject_le_fourPointFourRoot_sq hn ho hc hGRH hL8 hL16
  have hs := LLS.PaperStatements.fullEndpoint_fourPointFour_sq_lt_level_sq hL8 hL16 hu
  exact ⟨p, hp, hpx, hpx.trans_lt hs, hpow, hall⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
