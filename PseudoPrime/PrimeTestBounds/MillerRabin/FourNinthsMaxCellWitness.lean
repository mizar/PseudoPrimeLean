/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsSquareBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsMaxCell

/-! # Square-input witness for the largest analytic cell -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, an odd square `n = p ^ 2` in the largest certified logarithmic
cell has a prime MR rejecting base at most `(4 / 9) * log n ^ 2`. The scalar
certificate supplies prime count, product size, and kernel count, which are
transported through the local prime-power witness criterion. -/
theorem exists_prime_witness_max_square_cell {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hRH : RiemannHypothesis)
    (hlo : (101149 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 54461 / 50) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hsize : (78 : ℝ) * Real.log 428403 < Real.log n := fourNinths_maxCell_size.2.trans_le hlo
  have hcount : Real.log n < 2 * Real.log (Nat.choose 32205 78 : ℝ) :=
    hhi.trans_lt fourNinths_maxCell_count_log
  have hnonneg : (0 : ℝ) ≤ 101149 / 100 := by norm_num only
  have hsq := pow_le_pow_left₀ hnonneg hlo 2
  have hbound : (428403 : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 := by
    nlinarith only [fourNinths_maxCell_size.1, hsq]
  exact
    square_witness_of_choose_bounds hn ho hp hp2 hpow (by norm_num only)
      (fourNinths_maxCell_primeCount hRH) hsize hcount hbound

end PseudoPrime.PrimeTestBounds.MillerRabin
