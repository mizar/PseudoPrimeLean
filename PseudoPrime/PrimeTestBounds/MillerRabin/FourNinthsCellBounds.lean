/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsSquareBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsSemiprimeBounds

/-! # Witness transfer from closed logarithmic cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A closed square cell with the distinct-prime scalar budgets yields a
four-ninths witness. Monotonicity transfers the endpoint conditions to the
input, and the square counting criterion gives the rejecting prime. -/
theorem square_cell_choose {n p B M k : ℕ} {a b : ℝ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hB : 1 < B) (hpi : M ≤ B.primeCounting) (ha : 0 ≤ a)
    (hlo : a ≤ Real.log n) (hhi : Real.log n ≤ b) (hsize : (k : ℝ) * Real.log B < a)
    (hcount : b < 2 * Real.log (Nat.choose M k : ℝ)) (hbound : 9 * (B : ℝ) ≤ 4 * a ^ 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hs := hsize.trans_le hlo
  have hc := hhi.trans_lt hcount
  have hsq := pow_le_pow_left₀ ha hlo 2
  have hB' : (B : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hbound, hsq]
  exact square_witness_of_choose_bounds hn ho hp hp2 hpow hB hpi hs hc hB'

/-- A closed square cell with repeated-prime scalar budgets yields a
four-ninths witness. The multichoose count retains repeated factors; the
endpoint inequalities transfer to the input through the square criterion. -/
theorem square_cell_multichoose {n p B M k : ℕ} {a b : ℝ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hB : 1 < B) (hpi : M ≤ B.primeCounting) (ha : 0 ≤ a)
    (hlo : a ≤ Real.log n) (hhi : Real.log n ≤ b) (hsize : (k : ℝ) * Real.log B < a)
    (hcount : b < 2 * Real.log (Nat.choose (M + k) k : ℝ)) (hbound : 9 * (B : ℝ) ≤ 4 * a ^ 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hs := hsize.trans_le hlo
  have hc := hhi.trans_lt hcount
  have hsq := pow_le_pow_left₀ ha hlo 2
  have hB' : (B : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hbound, hsq]
  exact square_witness_of_multichoose_bounds hn ho hp hp2 hpow hB hpi hs hc hB'

/-- A closed semiprime cell with distinct-prime budgets yields a four-ninths
witness in the large-`q` branch. Transfer both endpoint bounds to the input,
then apply the local gcd criterion with the two-thirds split. -/
theorem semiprime_cell_choose {n p q B M k : ℕ} {a b : ℝ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hB : 1 < B) (hpi : M ≤ B.primeCounting)
    (ha : 0 ≤ a) (hlo : a ≤ Real.log n) (hhi : Real.log n ≤ b)
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q)
    (hsize : (k : ℝ) * Real.log B ≤ (2 / 3 : ℝ) * a)
    (hcount : b / 3 ≤ Real.log (Nat.choose M k : ℝ)) (hbound : 9 * (B : ℝ) ≤ 4 * a ^ 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hs : (k : ℝ) * Real.log B ≤ (2 / 3 : ℝ) * Real.log n := by linarith only [hsize, hlo]
  have hc : (1 / 3 : ℝ) * Real.log n ≤ Real.log (Nat.choose M k : ℝ) := by
    linarith only [hcount, hhi]
  have hsq := pow_le_pow_left₀ ha hlo 2
  have hB' : (B : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hbound, hsq]
  exact semiprime_large_choose hn ho hp hq hq2 hprod hB hpi hqLarge hs hc hB'

/-- The repeated-prime version of the closed semiprime cell criterion.
The same endpoint transfer applies to the multichoose count, which is needed
in the low range of the large-`q` branch. -/
theorem semiprime_cell_multichoose {n p q B M k : ℕ} {a b : ℝ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hB : 1 < B)
    (hpi : M ≤ B.primeCounting) (ha : 0 ≤ a) (hlo : a ≤ Real.log n) (hhi : Real.log n ≤ b)
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q)
    (hsize : (k : ℝ) * Real.log B ≤ (2 / 3 : ℝ) * a)
    (hcount : b / 3 ≤ Real.log (Nat.choose (M + k) k : ℝ)) (hbound : 9 * (B : ℝ) ≤ 4 * a ^ 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hs : (k : ℝ) * Real.log B ≤ (2 / 3 : ℝ) * Real.log n := by linarith only [hsize, hlo]
  have hc : (1 / 3 : ℝ) * Real.log n ≤ Real.log (Nat.choose (M + k) k : ℝ) := by
    linarith only [hcount, hhi]
  have hsq := pow_le_pow_left₀ ha hlo 2
  have hB' : (B : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hbound, hsq]
  exact semiprime_large_multichoose hn ho hp hq hq2 hprod hB hpi hqLarge hs hc hB'

end PseudoPrime.PrimeTestBounds.MillerRabin
