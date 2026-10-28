/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FullEndpointFixed61
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointEvenPolynomial

/-! # Strong-MR prime witnesses at most 61 through log n=286/25 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A prime below 67 is at most 61. The five integers from 62 through 66
are certified composite by a kernel check. This rounds a fixed radius bound
and does not enumerate any input integer n. -/
theorem prime_lt67_le61 {p : ℕ} (hp : p.Prime) (h : p < 67) : p ≤ 61 := by
  have hcheck : ∀ k ∈ Finset.Icc 62 66, ¬Nat.Prime k := by decide +kernel
  by_contra hn
  exact hcheck p (Finset.mem_Icc.mpr ⟨Nat.lt_of_not_ge hn, Nat.le_of_lt_succ h⟩) hp

/-- Under GRH, an odd composite n>1 with log n<=286/25 has a rejecting prime at most 61.
Use the positive exact gap at radius 49/6, then round primes below 67 to 61.
The conclusion uses the actual strong-MR rejection predicate. -/
theorem exists_prime_endpoint61 {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 286 / 25) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 61 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hpow, hrest⟩ :=
    exists_prime_reject_of_even_exact_endpoint_gap_pos hn ho hc hGRH
      (by norm_num only : (8 : ℝ) ≤ 49 / 6) (LLS.PaperStatements.endpoint61_gap_pos hL)
  have h67 : (p : ℝ) < 67 := lt_of_le_of_lt hb (by norm_num only)
  have hp61 := prime_lt67_le61 hp (by exact_mod_cast h67)
  exact ⟨p, hp, by exact_mod_cast hp61, PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hrest⟩⟩

/-- Under the fixed-61 theorem assumptions, the least rejecting prime is at most 61.
Apply the existing least-prime extraction to the prime witness theorem.
No lower logarithmic threshold is imposed. -/
theorem exists_least_endpoint61 {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 286 / 25) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 61 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  exact exists_least_prime_reject_of_exists_prime_reject (exists_prime_endpoint61 hn ho hc hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
