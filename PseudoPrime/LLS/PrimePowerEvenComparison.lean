/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PrimePowerComparison

/-!
# Odd-prime even-power comparisons for LLS Lemma 5.1

The actual finite even-tail weights are bounded by their geometric-series mass.
The first weight dominates this mass for prime three and all larger primes;
this proves their local comparison for unit-norm character values.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For real `p > 1`, the normalized even-power majorants have sum
`2p²/(p²-1)²`. Add the geometric and linear-times-geometric series at ratio `1/p²`.
This is the exact mass used for the odd-prime comparison in Lemma 5.1. -/
theorem hasSum_even_power_majorant {p : ℝ} (hp : 1 < p) :
    HasSum (fun j : ℕ ↦ 2 * ((j : ℝ) + 1) / p ^ (2 * (j + 1))) (2 * p ^ 2 / (p ^ 2 - 1) ^ 2) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hp2 : 1 < p ^ 2 := one_lt_pow₀ hp (by decide)
  have hr : ‖(1 / p ^ 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (sq_pos_of_pos hp0))]
    apply (div_lt_iff₀ (sq_pos_of_pos hp0)).mpr
    simpa only [one_mul] using hp2
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hr).add (hasSum_geometric_of_norm_lt_one hr)
  have ht := hs.mul_left (2 / p ^ 2)
  convert ht using 1
  · ext j
    rw [pow_mul, pow_succ, div_pow]
    norm_num only [one_pow]
    field_simp
  · field_simp [hp0.ne', (by nlinarith only [hp2] : p ^ 2 - 1 ≠ 0)]
    ring

/-- For `p > 1`, every finite set of normalized even-power terms has mass at most
`2p²/(p²-1)²`. Nonnegativity bounds the finite sum by the convergent infinite sum.
This supplies a bound uniform in the exponent cutoff. -/
theorem even_power_majorant_sum_le {p : ℝ} (hp : 1 < p) (s : Finset ℕ) :
    ∑ j ∈ s, 2 * ((j : ℝ) + 1) / p ^ (2 * (j + 1)) ≤ 2 * p ^ 2 / (p ^ 2 - 1) ^ 2 := by
  have hs := hasSum_even_power_majorant hp
  have h :=
    hs.summable.sum_le_tsum s
      (fun j _ ↦
        div_nonneg
          (mul_nonneg (by norm_num only) (add_nonneg (Nat.cast_nonneg j) (by norm_num only)))
          (pow_nonneg (zero_le_one.trans hp.le) _))
  rw [hs.tsum_eq] at h
  exact h

/-- For real `p ≥ 4`, the even-power mass is at most `1/p-1/p²`.
Clear positive denominators and use nonnegative powers of `p-4` to certify the
polynomial inequality. This fits below the first-weight margin when `p² ≤ x`. -/
theorem even_power_mass_le_first_margin {p : ℝ} (hp : 4 ≤ p) :
    2 * p ^ 2 / (p ^ 2 - 1) ^ 2 ≤ 1 / p - 1 / p ^ 2 := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 4) hp
  have hd : 0 < (p ^ 2 - 1) ^ 2 := sq_pos_of_pos (by nlinarith only [hp])
  have he : 1 / p - 1 / p ^ 2 = (p - 1) / p ^ 2 := by field_simp
  rw [he]
  apply (div_le_div_iff₀ hd (sq_pos_of_pos hp0)).mpr
  have hy : 0 ≤ p - 4 := sub_nonneg.mpr hp
  have h2 := sq_nonneg (p - 4)
  have h3 := pow_nonneg hy 3
  have h4 := pow_nonneg hy 4
  have h5 := pow_nonneg hy 5
  nlinarith only [hy, h2, h3, h4, h5]

/-- For a prime, positive exponent, and `x > 1`, the quadratic actual weight is at
most `k/p^k`. The common cutoff correction is nonnegative. Cancel the positive index;
this removes the logarithms from the even-tail estimate without GRH. -/
theorem prime_power_weight_majorant {x : ℝ} (hx : 1 < x) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    (k : ℝ) ^ 2 * primePowerComparisonWeight x p k ≤ (k : ℝ) / (p : ℝ) ^ k := by
  have ht : 0 ≤ Real.log p / (x * Real.log x) :=
    div_nonneg (Real.log_pos (by exact_mod_cast hp.one_lt)).le
      (mul_pos (zero_lt_one.trans hx) (Real.log_pos hx)).le
  rw [primePowerComparisonWeight_eq hp hk]
  have h :=
    mul_le_mul_of_nonneg_left (sub_le_self (1 / ((k : ℝ) * (p : ℝ) ^ k)) ht) (sq_nonneg (k : ℝ))
  have he : (k : ℝ) ^ 2 * (1 / ((k : ℝ) * (p : ℝ) ^ k)) = (k : ℝ) / (p : ℝ) ^ k := by
    field_simp [Nat.cast_ne_zero.mpr hk]
  rw [he] at h
  exact h

/-- For a prime and `x > 1`, any finite quadratic even-weight sum is bounded by
`2p²/(p²-1)²`. Apply the pointwise majorant and the exact geometric-series mass.
This connects the actual paper weights to the odd-prime comparison. -/
theorem prime_power_weighted_even_sum_le {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime)
    (s : Finset ℕ) :
    ∑ j ∈ s, (((2 * (j + 1) : ℕ) : ℝ) ^ 2 * primePowerComparisonWeight x p (2 * (j + 1))) ≤
      2 * (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1) ^ 2 := by
  apply
    le_trans
      (Finset.sum_le_sum
        (fun j _ ↦
          prime_power_weight_majorant hx hp (Nat.mul_ne_zero (by decide) (Nat.succ_ne_zero j))))
  simpa only [Nat.cast_mul, Nat.cast_succ, Nat.cast_zero, zero_add, one_add_one_eq_two] using
    even_power_majorant_sum_le (p := (p : ℝ)) (by exact_mod_cast hp.one_lt) s

/-- For `x > 1` and a prime `p ≤ x`, the first paper weight is at least `1/p-1/x`.
Monotonicity gives `log p ≤ log x`, so its cutoff correction is at most `1/x`.
This is the positive head margin needed against the even-power tail. -/
theorem prime_power_first_weight_lower {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p.Prime)
    (hpx : (p : ℝ) ≤ x) : 1 / (p : ℝ) - 1 / x ≤ primePowerComparisonWeight x p 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hx0 := zero_lt_one.trans hx
  have hlx := Real.log_pos hx
  have hl := Real.log_le_log hp0 hpx
  have ht := div_le_div_of_nonneg_right hl (mul_pos hx0 hlx).le
  have he : Real.log x / (x * Real.log x) = 1 / x := by field_simp
  rw [primePowerComparisonWeight_eq hp (by decide : 1 ≠ 0)]
  simp only [Nat.cast_one, one_mul, pow_one]
  rw [he] at ht
  linarith only [ht]

/-- For `x ≥ 100`, the first prime-three weight dominates its complete even-power mass.
The first-weight bound and `1/x ≤ 1/100` give the rational comparison.
This handles the exceptional odd prime in Lemma 5.1. -/
theorem prime_three_even_mass_le_first_weight {x : ℝ} (hx : 100 ≤ x) :
    2 * (3 : ℝ) ^ 2 / ((3 : ℝ) ^ 2 - 1) ^ 2 ≤ primePowerComparisonWeight x 3 1 := by
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 100) hx
  have h :=
    prime_power_first_weight_lower hx1 Nat.prime_three
      (le_trans (by norm_num only : (3 : ℝ) ≤ 100) hx)
  have hi := one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 100) hx
  norm_num only at h ⊢
  linarith only [h, hi]

/-- For prime `p ≥ 4` with `p² ≤ x`, its first weight dominates its even-power mass.
Compare `1/x` to `1/p²` and apply the mass polynomial certificate.
This removes the numerical comparison assumption from the large-prime branch. -/
theorem prime_large_even_mass_le_first_weight {x : ℝ} {p : ℕ} (hp : p.Prime) (hp4 : 4 ≤ p)
    (hpx : (p : ℝ) ^ 2 ≤ x) :
    2 * (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1) ^ 2 ≤ primePowerComparisonWeight x p 1 := by
  have hpr : (4 : ℝ) ≤ p := by exact_mod_cast hp4
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs : (p : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith only [hpr]
  have hx1 : 1 < x := lt_of_lt_of_le (by nlinarith only [hpr]) hpx
  have h := prime_power_first_weight_lower hx1 hp (hs.trans hpx)
  have hi := one_div_le_one_div_of_le (sq_pos_of_pos hp0) hpx
  exact (even_power_mass_le_first_margin hpr).trans (by linarith only [h, hi])

/-- For prime `p ≥ 3`, `x ≥ 100`, `p² ≤ x`, and a unit-norm complex value,
the first comparison term plus any finite even tail within the cutoff is nonnegative.
Weight positivity, the power-real-part bound, and the first-weight mass estimate prove
this local comparison. Odd terms beyond the first can subsequently be added nonnegatively. -/
theorem prime_odd_head_even_tail_nonneg {x : ℝ} (hx : 100 ≤ x) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hpx : (p : ℝ) ^ 2 ≤ x) {z : ℂ} (hz : ‖z‖ = 1) (s : Finset ℕ)
    (hcut : ∀ j ∈ s, (p : ℝ) ^ (2 * (j + 1)) ≤ x) :
    0 ≤
      (1 + z.re) * primePowerComparisonWeight x p 1 +
        ∑ j ∈ s, primePowerComparisonWeight x p (2 * (j + 1)) * ((z ^ (2 * (j + 1))).re - 1) := by
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 100) hx
  have hm : 2 * (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1) ^ 2 ≤ primePowerComparisonWeight x p 1 := by
    rcases Nat.eq_or_lt_of_le hp3 with he | hl
    · subst p
      exact prime_three_even_mass_le_first_weight hx
    · exact prime_large_even_mass_le_first_weight hp (Nat.succ_le_of_lt hl) hpx
  have ha := Complex.abs_re_le_norm z
  rw [hz] at ha
  have hn : 0 ≤ 1 + z.re := by linarith only [neg_le_of_abs_le ha]
  have ht := prime_power_weighted_even_sum_le hx1 hp s
  have hs :
    -(1 + z.re) *
        (∑ j ∈ s, (((2 * (j + 1) : ℕ) : ℝ) ^ 2 * primePowerComparisonWeight x p (2 * (j + 1)))) ≤
      ∑ j ∈ s, primePowerComparisonWeight x p (2 * (j + 1)) * ((z ^ (2 * (j + 1))).re - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have he : Even (2 * (j + 1)) := ⟨j + 1, by ring⟩
    have hw :=
      primePowerComparisonWeight_nonneg
        (one_lt_pow₀ (by exact_mod_cast hp.one_lt : (1 : ℝ) < p)
          (Nat.mul_ne_zero (by decide) (Nat.succ_ne_zero j)))
        (hcut j hj)
    have h := mul_le_mul_of_nonneg_left (Analysis.even_power_difference_le hz he) hw
    nlinarith only [h]
  have hc := mul_nonneg hn (sub_nonneg.mpr (le_trans ht hm))
  nlinarith only [hs, hc]

/-- For prime `p ≥ 3`, `p ≤ x`, `x ≥ 100`, and unit-norm `z`, the first term plus
any finite even tail within the cutoff is nonnegative. A nonempty tail implies `p² ≤ x`;
an empty tail uses the first weight's nonnegativity. This removes the auxiliary
square-cutoff premise. -/
theorem prime_odd_head_even_tail_nonneg_of_cutoff {x : ℝ} (hx : 100 ≤ x) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 ≤ p) (hpx : (p : ℝ) ≤ x) {z : ℂ} (hz : ‖z‖ = 1) (s : Finset ℕ)
    (hcut : ∀ j ∈ s, (p : ℝ) ^ (2 * (j + 1)) ≤ x) :
    0 ≤
      (1 + z.re) * primePowerComparisonWeight x p 1 +
        ∑ j ∈ s, primePowerComparisonWeight x p (2 * (j + 1)) * ((z ^ (2 * (j + 1))).re - 1) := by
  by_cases hs : s.Nonempty
  · obtain ⟨j, hj⟩ := hs
    have hr : (1 : ℝ) ≤ p := (by exact_mod_cast hp.one_lt : (1 : ℝ) < p).le
    have he : 2 ≤ 2 * (j + 1) := Nat.le_mul_of_pos_right 2 (Nat.succ_pos j)
    exact
      prime_odd_head_even_tail_nonneg hx hp hp3 ((pow_le_pow_right₀ hr he).trans (hcut j hj)) hz s
        hcut
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.sum_empty, add_zero]
    have hn := neg_le_of_abs_le (Complex.abs_re_le_norm z)
    rw [hz] at hn
    exact
      mul_nonneg (by linarith only [hn])
        (primePowerComparisonWeight_nonneg
          (by simpa only [pow_one] using (show (1 : ℝ) < p by exact_mod_cast hp.one_lt))
          (by simpa only [pow_one] using hpx))

end PseudoPrime.LLS.PaperStatements
