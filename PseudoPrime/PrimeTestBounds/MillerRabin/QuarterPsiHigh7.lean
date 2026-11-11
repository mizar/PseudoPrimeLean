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
private theorem prime_count_53584 :
    letI : ∀ n : ℕ, Decidable n.Prime := Nat.decidablePrime'
    ((Finset.Ioc 50000 53583).filter Nat.Prime).card = 325 := by
  decide +kernel

set_option maxRecDepth 20000 in
-- The count covers every integer in the finite interval from 50001 to 53583.
/-- A certified prime count above 50000 bounds `psi` below on `[53584, 54057)`.
The proof combines the 50000 anchor with monotonicity of `psi`. -/
theorem psi_lower_53584_54057 {x : ℝ} (ha : (53584 : ℝ) ≤ x) (hb : x < 54057) :
    x - 600 ≤ Chebyshev.psi x := by
  classical
  have h := psi_lower_prime_count (show 50000 ≤ 53583 by decide)
  rw [← Finset.filter_congr_decidable _ Nat.Prime Nat.decidablePrime'] at h
  rw [prime_count_53584] at h
  norm_num only at h
  have hm := Chebyshev.psi_mono (show (53583 : ℝ) ≤ x by linarith only [ha])
  linarith only [h, hm, hb]

end PseudoPrime.PrimeTestBounds.MillerRabin
