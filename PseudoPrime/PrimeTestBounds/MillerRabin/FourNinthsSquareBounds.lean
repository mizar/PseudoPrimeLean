/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsPrimeCount

/-! # Logarithmic counting conditions for square inputs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `n = p ^ 2`, logarithmic size and binomial-count inequalities imply
`B ^ k < p ^ 2` and `p - 1 < choose M k`. Positivity and monotonicity of
the real logarithm recover the natural inequalities. This connects analytic
square cells to the local prime-power witness criterion. -/
theorem square_choose_of_log_bounds {n p B M k : ℕ} (hp : p.Prime) (hn : n = p ^ 2) (hB : 1 < B)
    (hsize : (k : ℝ) * Real.log B < Real.log n)
    (hcount : Real.log n < 2 * Real.log (Nat.choose M k : ℝ)) :
    B ^ k < p ^ 2 ∧ p - 1 < Nat.choose M k := by
  have hpos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hnpos : (0 : ℝ) < n := by
    rw [hn, Nat.cast_pow]
    exact pow_pos hpos _
  have hsize' : Real.log ((B : ℝ) ^ k) < Real.log (n : ℝ) := by
    rw [Real.log_pow]
    exact hsize
  have hlt : (B : ℝ) ^ k < (n : ℝ) :=
    (Real.log_lt_log_iff (pow_pos (Nat.cast_pos.mpr (zero_lt_one.trans hB)) _) hnpos).mp hsize'
  have hpLog : Real.log n = 2 * Real.log p := by
    rw [hn, Nat.cast_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hcpos : 0 < Nat.choose M k := by
    by_contra h
    have hz : Nat.choose M k = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.cast_zero, Real.log_zero] at hcount
    have hpn := Real.log_natCast_nonneg p
    linarith only [hcount, hpLog, hpn]
  have hclog : Real.log (p : ℝ) < Real.log (Nat.choose M k : ℝ) := by linarith only [hcount, hpLog]
  have hpc : (p : ℝ) < (Nat.choose M k : ℝ) :=
    (Real.log_lt_log_iff hpos (Nat.cast_pos.mpr hcpos)).mp hclog
  have hnat : B ^ k < n := by exact_mod_cast hlt
  exact ⟨hn ▸ hnat, (Nat.sub_le p 1).trans_lt (Nat.cast_lt.mp hpc)⟩

/-- For an odd square, the distinct-prime count and the three cell inequalities
give a prime MR witness within the four-ninths bound. Convert the logarithmic
conditions to local kernel conditions and apply the prime-count interface. -/
theorem square_witness_of_choose_bounds {n p B M k : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hB : 1 < B) (hprimecount : M ≤ B.primeCounting)
    (hsize : (k : ℝ) * Real.log B < Real.log n)
    (hcount : Real.log n < 2 * Real.log (Nat.choose M k : ℝ))
    (hbound : (B : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨hs, hc⟩ := square_choose_of_log_bounds hp hpow hB hsize hcount
  have hdiv : p ^ 2 ∣ n := hpow.symm ▸ dvd_refl (p ^ 2)
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_primePow_choose_count hn ho hp hp2 (by norm_num only : 0 < 2) hdiv B M k
      hprimecount hs hc
  exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hbound, hf⟩

/-- The repeated-prime analogue of the square cell criterion. The bound
`choose (M + k) k` counts products with multiplicity and supplies the local
kernel contradiction required for the low square cells. -/
theorem square_witness_of_multichoose_bounds {n p B M k : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hB : 1 < B) (hprimecount : M ≤ B.primeCounting)
    (hsize : (k : ℝ) * Real.log B < Real.log n)
    (hcount : Real.log n < 2 * Real.log (Nat.choose (M + k) k : ℝ))
    (hbound : (B : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨hs, hc⟩ := square_choose_of_log_bounds hp hpow hB hsize hcount
  have hdiv : p ^ 2 ∣ n := hpow.symm ▸ dvd_refl (p ^ 2)
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_primePow_multichoose_count hn ho hp hp2 (by norm_num only : 0 < 2) hdiv B M k hB
      hprimecount hs hc
  exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hbound, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
