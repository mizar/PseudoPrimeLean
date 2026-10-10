/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CosetRootBounds

/-! # Finite root certificates for small composite prime-power exponents

Exact natural-power and square certificates majorize the roots at cutoff
one billion. The fixed exponent range is checked by the Lean kernel.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The integer ceilings for the root and its square root at cutoff `10^9`,
indexed by exponent. Entries for exponents three through twenty-eight are
used in the finite majorant; other indices return a dummy pair `(1,1)`.
The following certificates verify both bounds and their total weighted cost. -/
private def smallRootCeilings (k : ℕ) : ℕ × ℕ :=
  ([(1, 1), (1, 1), (1, 1), (1000, 32), (178, 14), (64, 8), (32, 6), (20, 5), (14, 4), (10, 4),
        (8, 3), (7, 3), (6, 3), (5, 3), (5, 3), (4, 2), (4, 2), (4, 2), (4, 2), (4, 2), (3, 2),
        (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2)]).getD
    k (1, 1)

/-- For each exponent three through twenty-eight, the table's first entry
has its `k`th power at least `10^9`, and its second entry has square at least
the first. Exact finite arithmetic checks the integer certificates.
They give real root upper bounds without evaluating irrational powers. -/
private theorem smallRootCeilings_valid :
    ∀ k ∈ Finset.Icc 3 28,
      1000000000 ≤ (smallRootCeilings k).1 ^ k ∧
        (smallRootCeilings k).1 ≤ (smallRootCeilings k).2 ^ 2 := by
  decide

/-- The weighted cost of the certified integer ceilings is at most `120000`.
Division by twenty gives the real finite-prefix majorant `6000`.
This is an exact finite arithmetic certificate. -/
private theorem smallRootCeilings_cost :
    (∑ k ∈ Finset.Icc 3 28, k * (20 * (smallRootCeilings k).1 + (smallRootCeilings k).2)) ≤
      120000 := by
  decide

/-- At cutoff `10^9`, the sum of root slices for exponents three through
twenty-eight is at most `6000`. Convert the exact integer power and square
certificates to real root bounds and sum their weighted costs.
This supplies the fixed finite part of the composite prime-power majorant. -/
theorem smallRootPrefix_le_six_thousand :
    (∑ k ∈ Finset.Icc (3 : ℕ) 28,
        (k : ℝ) *
          ((1000000000 : ℝ) ^ ((1 : ℝ) / k) + Real.sqrt ((1000000000 : ℝ) ^ ((1 : ℝ) / k)) / 20)) ≤
      6000 := by
  have hpoint (k : ℕ) (hk : k ∈ Finset.Icc 3 28) :
    (k : ℝ) *
        ((1000000000 : ℝ) ^ ((1 : ℝ) / k) + Real.sqrt ((1000000000 : ℝ) ^ ((1 : ℝ) / k)) / 20) ≤
      (k : ℝ) * (20 * (smallRootCeilings k).1 + (smallRootCeilings k).2) / 20 := by
    have hc := smallRootCeilings_valid k hk
    have hk0 : 0 < k := lt_of_lt_of_le (by norm_num only) (Finset.mem_Icc.mp hk).1
    have hr :=
      root_le_of_le_nat_pow (by norm_num only : (0 : ℝ) ≤ 1000000000)
        (Nat.cast_nonneg (smallRootCeilings k).1) hk0 (by exact_mod_cast hc.1)
    have hsq : ((smallRootCeilings k).1 : ℝ) ≤ ((smallRootCeilings k).2 : ℝ) ^ 2 := by
      exact_mod_cast hc.2
    have hs := Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg (smallRootCeilings k).2, hr.trans hsq⟩
    have hterm :
      (1000000000 : ℝ) ^ ((1 : ℝ) / k) + Real.sqrt ((1000000000 : ℝ) ^ ((1 : ℝ) / k)) / 20 ≤
        (20 * (smallRootCeilings k).1 + (smallRootCeilings k).2) / 20 := by
      linarith only [hr, hs]
    have hm := mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    nlinarith only [hm]
  have hs := Finset.sum_le_sum hpoint
  rw [← Finset.sum_div] at hs
  have hc :
    ((∑ k ∈ Finset.Icc 3 28, k * (20 * (smallRootCeilings k).1 + (smallRootCeilings k).2) : ℕ) :
        ℝ) ≤
      120000 := by
    exact_mod_cast smallRootCeilings_cost
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hc
  linarith only [hs, hc]

/-- At every cutoff at least `10^9`, root slices for exponents three through
twenty-eight sum to at most `19 sqrt x/100`. Normalize by `sqrt x`,
transfer to the base cutoff, and apply the exact finite certificate.
This bounds the fixed finite part uniformly over all large cutoffs. -/
theorem smallRootPrefix_le_sqrt_fraction {x : ℝ} (hx : 1000000000 ≤ x) :
    (∑ k ∈ Finset.Icc (3 : ℕ) 28,
        (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)) ≤
      (19 / 100 : ℝ) * Real.sqrt x := by
  have hb : (0 : ℝ) < 1000000000 := by norm_num only
  have hxb : 0 < Real.sqrt x := Real.sqrt_pos.mpr (hb.trans_le hx)
  have hbb : 0 < Real.sqrt (1000000000 : ℝ) := Real.sqrt_pos.mpr hb
  have hr :
    (∑ k ∈ Finset.Icc (3 : ℕ) 28,
          (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)) /
        Real.sqrt x ≤
      (∑ k ∈ Finset.Icc (3 : ℕ) 28,
          (k : ℝ) *
            ((1000000000 : ℝ) ^ ((1 : ℝ) / k) +
              Real.sqrt ((1000000000 : ℝ) ^ ((1 : ℝ) / k)) / 20)) /
        Real.sqrt (1000000000 : ℝ) := by
    rw [Finset.sum_div, Finset.sum_div]
    exact
      Finset.sum_le_sum fun k hk =>
        rootSlice_div_sqrt_le_at_base hb hx
          ((by norm_num only : 2 ≤ 3).trans (Finset.mem_Icc.mp hk).1)
  have hbase := div_le_div_of_nonneg_right smallRootPrefix_le_six_thousand hbb.le
  have hsqrt : (31600 : ℝ) ≤ Real.sqrt (1000000000 : ℝ) := Real.le_sqrt_of_sq_le (by norm_num only)
  have hc : (6000 : ℝ) / Real.sqrt (1000000000 : ℝ) ≤ 19 / 100 :=
    (div_le_iff₀ hbb).mpr (by linarith only [hsqrt])
  exact (div_le_iff₀ hxb).mp (hr.trans (hbase.trans hc))

/-- For a nonnegative logarithmic displacement `u`, the polynomial root-tail
majorant is at most `220 exp(27u/58)`. The quadratic lower bound on the
exponential dominates each polynomial coefficient.
The exponent is `1/2-1/29`, needed for the root tail after exponent twenty-eight. -/
theorem rootTailPolynomial_le_exp {u : ℝ} (hu : 0 ≤ u) :
    (21 / 20 : ℝ) * (21 / 10) * (((30 + (3 / 2 : ℝ) * u) * (31 + (3 / 2 : ℝ) * u)) / 2 - 406) ≤
      220 * Real.exp ((27 / 58 : ℝ) * u) := by
  have he := Real.quadratic_le_exp_of_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 27 / 58) hu)
  nlinarith only [he, hu, sq_nonneg u]

/-- The odd-exponent ceiling costs through twenty-eight sum to at most 85000.
Exact finite arithmetic checks the table. This bounds the nonsquare prefix. -/
private theorem oddSmallRootCeilings_cost :
    (∑ k ∈ (Finset.Icc 3 28).filter Odd,
        k * (20 * (smallRootCeilings k).1 + (smallRootCeilings k).2)) ≤
      85000 := by
  decide

/-- At cutoff one billion, the root slices for odd exponents three through
twenty-eight sum to at most 4250. Apply the exact root certificates and sum
only the odd table entries. This bounds the nonsquare prime-power prefix. -/
theorem smallOddRootPrefix_le_4250 :
    (∑ k ∈ (Finset.Icc (3 : ℕ) 28).filter Odd,
        (k : ℝ) *
          ((1000000000 : ℝ) ^ ((1 : ℝ) / k) + Real.sqrt ((1000000000 : ℝ) ^ ((1 : ℝ) / k)) / 20)) ≤
      4250 := by
  have hpoint (k : ℕ) (hk : k ∈ (Finset.Icc 3 28).filter Odd) :
    (k : ℝ) *
        ((1000000000 : ℝ) ^ ((1 : ℝ) / k) + Real.sqrt ((1000000000 : ℝ) ^ ((1 : ℝ) / k)) / 20) ≤
      (k : ℝ) * (20 * (smallRootCeilings k).1 + (smallRootCeilings k).2) / 20 := by
    have hc := smallRootCeilings_valid k (Finset.mem_filter.mp hk).1
    have hk0 : 0 < k :=
      lt_of_lt_of_le (by norm_num only) (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
    have hr :=
      root_le_of_le_nat_pow (by norm_num only : (0 : ℝ) ≤ 1000000000)
        (Nat.cast_nonneg (smallRootCeilings k).1) hk0 (by exact_mod_cast hc.1)
    have hsq : ((smallRootCeilings k).1 : ℝ) ≤ ((smallRootCeilings k).2 : ℝ) ^ 2 := by
      exact_mod_cast hc.2
    have hs := Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg (smallRootCeilings k).2, hr.trans hsq⟩
    have hterm :
      (1000000000 : ℝ) ^ ((1 : ℝ) / k) + Real.sqrt ((1000000000 : ℝ) ^ ((1 : ℝ) / k)) / 20 ≤
        (20 * (smallRootCeilings k).1 + (smallRootCeilings k).2) / 20 := by
      linarith only [hr, hs]
    have hm := mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    nlinarith only [hm]
  have hs := Finset.sum_le_sum hpoint
  rw [← Finset.sum_div] at hs
  have hc :
    ((∑ k ∈ (Finset.Icc 3 28).filter Odd,
            k * (20 * (smallRootCeilings k).1 + (smallRootCeilings k).2) :
          ℕ) :
        ℝ) ≤
      85000 := by
    exact_mod_cast oddSmallRootCeilings_cost
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hc
  linarith only [hs, hc]

/-- Above cutoff one billion, the odd-exponent root prefix through twenty-eight
is at most 27/200 times the cutoff square root. Normalize the root slices,
transfer to the base cutoff and use the odd finite certificate.
This leaves enough margin for the tail in the Section 4.1 nonsquare bound. -/
theorem smallOddRootPrefix_le_sqrt_fraction {x : ℝ} (hx : 1000000000 ≤ x) :
    (∑ k ∈ (Finset.Icc (3 : ℕ) 28).filter Odd,
        (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)) ≤
      (27 / 200 : ℝ) * Real.sqrt x := by
  have hb : (0 : ℝ) < 1000000000 := by norm_num only
  have hxb : 0 < Real.sqrt x := Real.sqrt_pos.mpr (hb.trans_le hx)
  have hbb : 0 < Real.sqrt (1000000000 : ℝ) := Real.sqrt_pos.mpr hb
  have hr :
    (∑ k ∈ (Finset.Icc (3 : ℕ) 28).filter Odd,
          (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)) /
        Real.sqrt x ≤
      (∑ k ∈ (Finset.Icc (3 : ℕ) 28).filter Odd,
          (k : ℝ) *
            ((1000000000 : ℝ) ^ ((1 : ℝ) / k) +
              Real.sqrt ((1000000000 : ℝ) ^ ((1 : ℝ) / k)) / 20)) /
        Real.sqrt (1000000000 : ℝ) := by
    rw [Finset.sum_div, Finset.sum_div]
    exact
      Finset.sum_le_sum fun k hk =>
        rootSlice_div_sqrt_le_at_base hb hx
          ((by norm_num only : 2 ≤ 3).trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1)
  have hbase := div_le_div_of_nonneg_right smallOddRootPrefix_le_4250 hbb.le
  have hsqrt : (31600 : ℝ) ≤ Real.sqrt (1000000000 : ℝ) := Real.le_sqrt_of_sq_le (by norm_num only)
  have hc : (4250 : ℝ) / Real.sqrt (1000000000 : ℝ) ≤ 27 / 200 :=
    (div_le_iff₀ hbb).mpr (by linarith only [hsqrt])
  exact (div_le_iff₀ hxb).mp (hr.trans (hbase.trans hc))

end PseudoPrime.LLS.PaperStatements
