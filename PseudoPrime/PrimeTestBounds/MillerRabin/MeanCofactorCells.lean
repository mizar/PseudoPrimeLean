/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanPrimeProducts
public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanThetaBounds

/-! # Large-cofactor counting with certified theta cells

The three applications below eliminate the theta hypotheses in the average-logarithm
criterion. The remaining prime-count, mean and binomial budgets are explicit arithmetic
conditions for the selected radius and subset size.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, the first certified theta cell supplies a rejecting prime for a large cofactor
when its explicit prime-count, mean and binomial budgets hold. Substitute the cell's theta
bounds into the general criterion. The hypotheses retain all floor and counting losses. -/
theorem large_cofactor_mean_cell_one (hRH : RiemannHypothesis) {n m q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hm : 1 < m) (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = m * q) (B M k : ℕ) (τ δ : ℝ)
    (hB : 52000 ^ 2 ≤ B) (hk : 1 ≤ k) (hM0 : 1 ≤ M) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (hmargin : 0 ≤ τ - δ)
    (hsize : τ ≤ Real.log q)
    (hM :
      (M : ℝ) ≤ (B : ℝ) * ((9968 / 10000) / Real.log B + (15 * (993 / 1000) / 16) / Real.log B ^ 2))
    (hmean : (k : ℝ) * ((10029 / 10000) * B) ≤ (τ - δ) * M) (hcount : τ * m < δ * Nat.choose M k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨hlo, hmid, hhi⟩ := mean_theta_cell_one hRH hB
  have hB' : 32 ≤ B := (by norm_num only : 32 ≤ 52000 ^ 2).trans hB
  exact
    large_cofactor_of_theta hn ho hm hq hq2 hprod B M k τ δ ((10029 / 10000) * B) (9968 / 10000)
      (993 / 1000) hB' hk hM0 hτ hδ hmargin hsize hlo hmid hhi hM hmean hcount

/-- Under RH, the second certified theta cell supplies a rejecting prime for a large
cofactor when its explicit prime-count, mean and binomial budgets hold. Substitute the
cell's theta bounds into the general criterion. -/
theorem large_cofactor_mean_cell_two (hRH : RiemannHypothesis) {n m q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hm : 1 < m) (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = m * q) (B M k : ℕ) (τ δ : ℝ)
    (hB : 650000 ^ 2 ≤ B) (hk : 1 ≤ k) (hM0 : 1 ≤ M) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (hmargin : 0 ≤ τ - δ)
    (hsize : τ ≤ Real.log q)
    (hM :
      (M : ℝ) ≤
        (B : ℝ) * ((9991 / 10000) / Real.log B + (15 * (9983 / 10000) / 16) / Real.log B ^ 2))
    (hmean : (k : ℝ) * ((10008 / 10000) * B) ≤ (τ - δ) * M) (hcount : τ * m < δ * Nat.choose M k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨hlo, hmid, hhi⟩ := mean_theta_cell_two hRH hB
  have hB' : 32 ≤ B := (by norm_num only : 32 ≤ 650000 ^ 2).trans hB
  exact
    large_cofactor_of_theta hn ho hm hq hq2 hprod B M k τ δ ((10008 / 10000) * B) (9991 / 10000)
      (9983 / 10000) hB' hk hM0 hτ hδ hmargin hsize hlo hmid hhi hM hmean hcount

/-- Under RH, the third certified theta cell supplies a rejecting prime for a large
cofactor when its explicit prime-count, mean and binomial budgets hold. Substitute the
cell's theta bounds into the general criterion. -/
theorem large_cofactor_mean_cell_three (hRH : RiemannHypothesis) {n m q : ℕ} (hn : 1 < n)
    (ho : Odd n) (hm : 1 < m) (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = m * q) (B M k : ℕ) (τ δ : ℝ)
    (hB : 65000000 ^ 2 ≤ B) (hk : 1 ≤ k) (hM0 : 1 ≤ M) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (hmargin : 0 ≤ τ - δ) (hsize : τ ≤ Real.log q)
    (hM :
      (M : ℝ) ≤
        (B : ℝ) * ((99992 / 100000) / Real.log B + (15 * (99984 / 100000) / 16) / Real.log B ^ 2))
    (hmean : (k : ℝ) * ((100008 / 100000) * B) ≤ (τ - δ) * M)
    (hcount : τ * m < δ * Nat.choose M k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨hlo, hmid, hhi⟩ := mean_theta_cell_three hRH hB
  have hB' : 32 ≤ B := (by norm_num only : 32 ≤ 65000000 ^ 2).trans hB
  exact
    large_cofactor_of_theta hn ho hm hq hq2 hprod B M k τ δ ((100008 / 100000) * B) (99992 / 100000)
      (99984 / 100000) hB' hk hM0 hτ hδ hmargin hsize hlo hmid hhi hM hmean hcount

end PseudoPrime.PrimeTestBounds.MillerRabin
