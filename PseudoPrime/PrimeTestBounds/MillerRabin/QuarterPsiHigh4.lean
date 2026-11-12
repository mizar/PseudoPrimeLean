/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiPrimeCount
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiPrimeCountAdd
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiCount1
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiCount2
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiCount3
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiCount4

/-! # Chebyshev lower bound from a finite prime-count certificate -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem prime_count_52048 :
    letI : ∀ n : ℕ, Decidable n.Prime := Nat.decidablePrime'
    ((Finset.Ioc 50000 52047).filter Nat.Prime).card = 189 := by
  rw [prime_count_Ioc_add 50000 51535 52047 (by decide) (by decide)]
  rw [prime_count_Ioc_add 50000 51023 51535 (by decide) (by decide)]
  rw [prime_count_Ioc_add 50000 50511 51023 (by decide) (by decide)]
  rw [prime_count_50000_50511, prime_count_50511_51023, prime_count_51023_51535,
    prime_count_51535_52047]

set_option maxRecDepth 20000 in
-- The count covers every integer in the finite interval from 50001 to 52047.
/-- A certified prime count above 50000 bounds `psi` below on `[52048, 52560)`.
The proof combines the 50000 anchor with monotonicity of `psi`. -/
theorem psi_lower_52048_52560 {x : ℝ} (ha : (52048 : ℝ) ≤ x) (hb : x < 52560) :
    x - 600 ≤ Chebyshev.psi x := by
  classical
  have h := psi_lower_prime_count (show 50000 ≤ 52047 by decide)
  rw [← Finset.filter_congr_decidable _ Nat.Prime Nat.decidablePrime'] at h
  rw [prime_count_52048] at h
  norm_num only at h
  have hm := Chebyshev.psi_mono (show (52047 : ℝ) ≤ x by linarith only [ha])
  linarith only [h, hm, hb]

end PseudoPrime.PrimeTestBounds.MillerRabin
