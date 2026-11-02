/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsHighSupply
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsSquareBounds

/-! # Uniform high-range witnesses for square inputs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, an odd square `n = p ^ 2` with `log n ≥ 1024` has a prime MR
rejecting base at most `(4 / 9) * log n ^ 2`. The selected square radius,
prime supply, and binomial budget satisfy the square witness criterion with
`σ = 1`; the argument covers the entire high half-line. -/
theorem exists_prime_witness_high_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hL : (1024 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let L := Real.log n
  let b := ⌊(2 / 3 : ℝ) * L⌋₊
  let B := b ^ 2
  let u := 2 * Real.log (b : ℝ)
  let M := ⌊((9 / 10 : ℝ) * (b : ℝ) ^ 2) / u⌋₊
  let k := ⌈(1 : ℝ) * L / u⌉₊ - 1
  have hb : 56 ≤ b := (high_radius_floor_lower hL).2.2
  have hB : 1 < B := by
    dsimp only [B]
    nlinarith only [hb]
  have hpi : M ≤ B.primeCounting := by
    have h := high_floor_radius_prime_count hRH hL
    simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using h
  have hbudget := high_selected_log_budgets (σ := (1 : ℝ)) hL (by norm_num only) (by norm_num only)
  have hs : (k : ℝ) * Real.log B < Real.log n := by
    simpa only [k, L, b, B, u, one_mul] using hbudget.1
  have hc : Real.log n < 2 * Real.log (Nat.choose M k : ℝ) := by
    have h : (1 : ℝ) * L / 2 < Real.log (Nat.choose M k : ℝ) := hbudget.2
    linarith only [h]
  have hbound : (B : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 := by
    dsimp only [B]
    rw [Nat.cast_pow]
    exact high_radius_floor_square_le hL
  exact square_witness_of_choose_bounds hn ho hp hp2 hpow hB hpi hs hc hbound

end PseudoPrime.PrimeTestBounds.MillerRabin
