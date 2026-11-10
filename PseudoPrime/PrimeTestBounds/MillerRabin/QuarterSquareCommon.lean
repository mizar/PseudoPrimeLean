/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed43Stage197
import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed89Stage197
import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed89Stage282
import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed89Stage358

/-! # Square-factor witnesses from independent weighted-count stages -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd input with a prime-square divisor of base at most 1054033525 has
 a rejecting prime at most 89. The proof dispatches independent weighted-count stages. -/
theorem square_reject_le1054 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hdiv : p ^ 2 ∣ n)
    (hbound : p ≤ 1054033525) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 89 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  by_cases h43 : p ≤ 43
  · exact
      ⟨p, hp, h43.trans (by decide), PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩
  · by_cases h809 : p ≤ 809
    · obtain ⟨r, hr, hb, hf⟩ :=
        exists_prime_reject_square_seed43 hn ho hp hdiv h809
          (square_factor_budget_77 (prime_ge_47_of_gt_43 hp (Nat.lt_of_not_ge h43)))
      exact ⟨r, hr, hb.trans (by decide), hf⟩
    · by_cases h19639 : p ≤ 19639
      · obtain ⟨r, hr, hb, hf⟩ :=
          exists_prime_reject_square_seed43_133 hn ho hp hdiv h19639
            (square_factor_budget_133 (Nat.succ_le_of_lt (Nat.lt_of_not_ge h809)))
        exact ⟨r, hr, hb.trans (by decide), hf⟩
      · by_cases h137 : p ≤ 1372508
        · exact
            exists_prime_reject_square_seed89_197 hn ho hp hdiv h137
              (square_factor_budget_197 (Nat.succ_le_of_lt (Nat.lt_of_not_ge h19639)))
        · by_cases h597 : p ≤ 59789534
          · exact
              exists_prime_reject_square_seed89_282 hn ho hp hdiv h597
                (square_factor_budget_282 (Nat.succ_le_of_lt (Nat.lt_of_not_ge h137)))
          · exact
              exists_prime_reject_square_seed89_358 hn ho hp hdiv hbound
                (square_factor_budget_358 (Nat.succ_le_of_lt (Nat.lt_of_not_ge h597)))

end PseudoPrime.PrimeTestBounds.MillerRabin
