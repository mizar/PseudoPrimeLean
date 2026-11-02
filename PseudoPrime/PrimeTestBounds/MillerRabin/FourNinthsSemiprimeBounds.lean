/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsPrimeCount
public import PseudoPrime.NumberTheory.ProductFermatKernel

/-! # Local kernel conditions for semiprime inputs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `n = p * q`, logarithmic bounds on a product radius and a count `C`
give `B ^ k < q` and put the local kernel gcd below `C`. Convert the log
inequalities using positivity, then bound the exact gcd by `p - 1`. This
supports both repeated and distinct prime-product semiprime cells. -/
theorem semiprime_kernel_of_log_bounds {n p q B C k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hprod : n = p * q) (hB : 1 < B) (hsize : (k : ℝ) * Real.log B < Real.log q)
    (hcount : Real.log p < Real.log (C : ℝ)) : B ^ k < q ∧ (q - 1).gcd (n - 1) < C := by
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr hq.pos
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr (zero_lt_one.trans hB)
  have hlog : Real.log ((B : ℝ) ^ k) < Real.log (q : ℝ) := by
    rw [Real.log_pow]
    exact hsize
  have hreal : (B : ℝ) ^ k < q := (Real.log_lt_log_iff (pow_pos hBpos _) hqpos).mp hlog
  have hnat : B ^ k < q := by exact_mod_cast hreal
  have hcpos : 0 < C := by
    by_contra h
    have hz : C = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.cast_zero, Real.log_zero] at hcount
    exact (not_lt_of_ge (Real.log_natCast_nonneg p)) hcount
  have hpchoose : p < C := by
    exact_mod_cast
      (Real.log_lt_log_iff (Nat.cast_pos.mpr hp.pos) (Nat.cast_pos.mpr hcpos)).mp hcount
  have hgcd : (q - 1).gcd (n - 1) ≤ p - 1 := by
    rw [hprod, Nat.mul_comm p q]
    exact NumberTheory.gcd_predecessor_product_le_cofactor hq.pos hp.one_lt
  exact ⟨hnat, hgcd.trans_lt ((Nat.sub_le p 1).trans_lt hpchoose)⟩

/-- A distinct-product count and logarithmic kernel conditions give a prime
MR witness within the four-ninths bound for `n = p * q`. Use the local kernel
at `q` and retain its gcd bound by the cofactor predecessor. -/
theorem semiprime_witness_of_choose_bounds {n p q B M k : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hB : 1 < B)
    (hpi : M ≤ B.primeCounting) (hsize : (k : ℝ) * Real.log B < Real.log q)
    (hcount : Real.log p < Real.log (Nat.choose M k : ℝ))
    (hbound : (B : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨hs, hc⟩ := semiprime_kernel_of_log_bounds hp hq hprod hB hsize hcount
  have hd : q ^ 1 ∣ n := by
    rw [pow_one, hprod]
    exact dvd_mul_left q p
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_choose_count_gcd hn ho hq hq2 (by norm_num only : 0 < 1) hd B M k hpi
      (by simpa only [pow_one] using hs) hc
  exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hbound, hf⟩

/-- The repeated-product version of the semiprime cell criterion. The
multichoose count includes repeated factors and yields the local kernel
contradiction needed in the low logarithmic range. -/
theorem semiprime_witness_of_multichoose_bounds {n p q B M k : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hB : 1 < B)
    (hpi : M ≤ B.primeCounting) (hsize : (k : ℝ) * Real.log B < Real.log q)
    (hcount : Real.log p < Real.log (Nat.choose (M + k) k : ℝ))
    (hbound : (B : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨hs, hc⟩ := semiprime_kernel_of_log_bounds hp hq hprod hB hsize hcount
  have hd : q ^ 1 ∣ n := by
    rw [pow_one, hprod]
    exact dvd_mul_left q p
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_multichoose_count_gcd hn ho hq hq2 (by norm_num only : 0 < 1) hd B M k hB hpi
      (by simpa only [pow_one] using hs) hc
  exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hbound, hf⟩

/-- In the large-`q` branch, `log q > (2/3) log n` and the distinct-product
cell conditions imply a four-ninths MR witness. The product logarithm puts
`log p` below `(1/3) log n`, and both kernel inequalities are strict. -/
theorem semiprime_large_choose {n p q B M k : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hB : 1 < B) (hpi : M ≤ B.primeCounting)
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q)
    (hsize : (k : ℝ) * Real.log B ≤ (2 / 3 : ℝ) * Real.log n)
    (hcount : (1 / 3 : ℝ) * Real.log n ≤ Real.log (Nat.choose M k : ℝ))
    (hbound : (B : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hlog : Real.log n = Real.log p + Real.log q := by
    rw [hprod, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero) (Nat.cast_ne_zero.mpr hq.ne_zero)]
  have hsmall : Real.log p < (1 / 3 : ℝ) * Real.log n := by linarith only [hlog, hqLarge]
  exact
    semiprime_witness_of_choose_bounds hn ho hp hq hq2 hprod hB hpi (hsize.trans_lt hqLarge)
      (hsmall.trans_le hcount) hbound

/-- The large-`q` semiprime branch with repeated prime factors. The same
two-thirds split supplies the strict local size and kernel inequalities;
multichoose supplies the product count needed by low cells. -/
theorem semiprime_large_multichoose {n p q B M k : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hB : 1 < B) (hpi : M ≤ B.primeCounting)
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q)
    (hsize : (k : ℝ) * Real.log B ≤ (2 / 3 : ℝ) * Real.log n)
    (hcount : (1 / 3 : ℝ) * Real.log n ≤ Real.log (Nat.choose (M + k) k : ℝ))
    (hbound : (B : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hlog : Real.log n = Real.log p + Real.log q := by
    rw [hprod, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero) (Nat.cast_ne_zero.mpr hq.ne_zero)]
  have hsmall : Real.log p < (1 / 3 : ℝ) * Real.log n := by linarith only [hlog, hqLarge]
  exact
    semiprime_witness_of_multichoose_bounds hn ho hp hq hq2 hprod hB hpi (hsize.trans_lt hqLarge)
      (hsmall.trans_le hcount) hbound

end PseudoPrime.PrimeTestBounds.MillerRabin
