/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsHighSupply
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsSemiprimeBounds

/-! # Uniform high-range witnesses for unbalanced semiprimes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, a semiprime `n = p * q` with `log n ≥ 1024` and
`log q > (2 / 3) * log n` has a prime MR rejecting base within the
four-ninths bound. The selected radius and binomial count satisfy the
semiprime kernel criterion with `σ = 2 / 3` on the whole high half-line. -/
theorem exists_prime_witness_high_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hL : (1024 : ℝ) ≤ Real.log n) (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let L := Real.log n
  let b := ⌊(2 / 3 : ℝ) * L⌋₊
  let B := b ^ 2
  let u := 2 * Real.log (b : ℝ)
  let M := ⌊((9 / 10 : ℝ) * (b : ℝ) ^ 2) / u⌋₊
  let k := ⌈(2 / 3 : ℝ) * L / u⌉₊ - 1
  have hb : 56 ≤ b := (high_radius_floor_lower hL).2.2
  have hB : 1 < B := by
    dsimp only [B]
    nlinarith only [hb]
  have hpi : M ≤ B.primeCounting := by
    have h := high_floor_radius_prime_count hRH hL
    simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using h
  have hbudget :=
    high_selected_log_budgets (σ := (2 / 3 : ℝ)) hL (by norm_num only) (by norm_num only)
  have hs : (k : ℝ) * Real.log B ≤ (2 / 3 : ℝ) * Real.log n := hbudget.1.le
  have hc : (1 / 3 : ℝ) * Real.log n ≤ Real.log (Nat.choose M k : ℝ) := by
    have h := hbudget.2
    linarith only [h]
  have hbound : (B : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 := by
    dsimp only [B]
    rw [Nat.cast_pow]
    exact high_radius_floor_square_le hL
  exact semiprime_large_choose hn ho hp hq hq2 hprod hB hpi hqLarge hs hc hbound

end PseudoPrime.PrimeTestBounds.MillerRabin
