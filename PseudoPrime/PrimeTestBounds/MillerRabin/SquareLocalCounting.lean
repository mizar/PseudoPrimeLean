/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareLogCounting

/-! # Square witnesses from reusable prime supplies -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For an odd prime square `n = p²`, a supply of at least `M` primes through
`B` and bounds `k log B ≤ u < log n ≤ 2v < 2 log choose(M+k,k)` give a prime
rejecting base at most `B`. Convert the strict logarithmic inequalities into
the repeated-prime product count. The prime supply can be reused at any degree
`k`, and the upper interval endpoint is included. -/
theorem exists_prime_reject_square_candidate {n p B M k : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hB : 1 < B) (hpi : M ≤ B.primeCounting)
    {u v : ℝ} (hsize : (k : ℝ) * Real.log B ≤ u) (hlo : u < Real.log n) (hhi : Real.log n ≤ 2 * v)
    (hcount : v < Real.log (Nat.choose (M + k) k : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hsize' : (k : ℝ) * Real.log B < Real.log n := hsize.trans_lt hlo
  have hcount' : Real.log n < 2 * Real.log (Nat.choose (M + k) k : ℝ) := by
    linarith only [hhi, hcount]
  obtain ⟨hs, hc⟩ := square_choose_of_log_bounds hp hpow hB hsize' hcount'
  have hdiv : p ^ 2 ∣ n := hpow.symm ▸ dvd_refl (p ^ 2)
  exact
    exists_prime_primePow_multichoose_count hn ho hp hp2 (by norm_num only : 0 < 2) hdiv B M k hB
      hpi hs hc

end PseudoPrime.PrimeTestBounds.MillerRabin
