/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiPrimeCount

/-! # Chebyshev lower bound from a finite prime-count certificate -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the finite interval using the minFac prime test.
private theorem prime_count_51024 :
    letI : ∀ n : ℕ, Decidable n.Prime := Nat.decidablePrime'
    ((Finset.Ioc 50000 51023).filter Nat.Prime).card = 90 := by
  decide +kernel

set_option maxRecDepth 20000 in
-- The count covers every integer in the finite interval from 50001 to 51023.
/-- A certified prime count above 50000 bounds `psi` below on `[51024, 51536)`.
The proof combines the 50000 anchor with monotonicity of `psi`. -/
theorem psi_lower_51024_51536 {x : ℝ} (ha : (51024 : ℝ) ≤ x) (hb : x < 51536) :
    x - 600 ≤ Chebyshev.psi x := by
  classical
  have h := psi_lower_prime_count (show 50000 ≤ 51023 by decide)
  rw [← Finset.filter_congr_decidable _ Nat.Prime Nat.decidablePrime'] at h
  rw [prime_count_51024] at h
  norm_num only at h
  have hm := Chebyshev.psi_mono (show (51023 : ℝ) ≤ x by linarith only [ha])
  linarith only [h, hm, hb]

end PseudoPrime.PrimeTestBounds.MillerRabin
