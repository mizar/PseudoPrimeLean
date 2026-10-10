/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CosetRootCertificates
public import Mathlib.Algebra.BigOperators.Intervals

/-! # Variable exponent tails in composite root sums

The exponent count is controlled by the logarithmic displacement above one
billion. Its quadratic growth is absorbed by a decreasing real power.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For endpoint `28+t`, the sum of real exponents from twenty-nine onward
is the full triangular sum minus `406`. Induction adds the next exponent.
This gives the polynomial count in the variable root tail. -/
theorem sum_rootTail_exponents (t : ℕ) :
    (∑ k ∈ Finset.Icc 29 (28 + t), (k : ℝ)) = (28 + (t : ℝ)) * (29 + (t : ℝ)) / 2 - 406 := by
  induction t with
  | zero =>
    norm_num only [Nat.add_zero, Nat.cast_zero, add_zero,
      Finset.Icc_eq_empty_of_lt (by norm_num only : 28 < 29), Finset.sum_empty]
  | succ t
    ih =>
    rw [Nat.add_succ, Nat.succ_eq_add_one,
      Finset.sum_Icc_succ_top
        (show 29 ≤ 28 + t + 1 by exact Nat.add_le_add_right (Nat.le_add_right 28 t) 1),
      ih]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-- Above cutoff `10^9`, the exponent endpoint is at most
`30 + 3 log(x/10^9)/2`. Compare the base with `2^30` and use `log 2 ≥ 2/3`.
This separates a fixed exponent count from its nonnegative displacement. -/
theorem rootExponentCutoff_le_displacement {x : ℝ} (hx : 1000000000 ≤ x) :
    (⌊Real.log x / Real.log 2⌋₊ : ℝ) ≤ 30 + (3 / 2 : ℝ) * Real.log (x / 1000000000) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hlx : 0 ≤ Real.log x := Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 1000000000).trans hx)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hf := Nat.floor_le (div_nonneg hlx hl2.le)
  have hu : 0 ≤ Real.log (x / 1000000000) :=
    Real.log_nonneg
      ((le_div_iff₀ (by norm_num only : (0 : ℝ) < 1000000000)).mpr
        (by simpa only [one_mul] using hx))
  have hb :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 1000000000)
      (by norm_num only : (1000000000 : ℝ) ≤ 2 ^ (30 : ℕ))
  rw [Real.log_pow] at hb
  norm_num only at hb
  have hl : Real.log (x / 1000000000) = Real.log x - Real.log 1000000000 :=
    Real.log_div hx0.ne' (by norm_num only)
  have hm :=
    mul_nonneg (show 0 ≤ (3 / 2 : ℝ) * Real.log 2 - 1 by linarith only [Real.log_two_gt_d9]) hu
  apply hf.trans
  apply (div_le_iff₀ hl2).mpr
  nlinarith only [hb, hl, hm]

/-- At cutoff at least `10^9`, all root slices with exponent at least
twenty-nine sum to at most `7 sqrt x/1000`. Bound each root by the twenty-ninth
root, count the exponents quadratically, and absorb logarithmic displacement
with the certified exponential majorant. This controls the variable tail in
the composite prime-power sum. -/
theorem rootTail_le_sqrt_fraction {x : ℝ} (hx : 1000000000 ≤ x) :
    (∑ k ∈ Finset.Icc 29 ⌊Real.log x / Real.log 2⌋₊,
        (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)) ≤
      (7 / 1000 : ℝ) * Real.sqrt x := by
  let K := ⌊Real.log x / Real.log 2⌋₊
  let u := Real.log (x / 1000000000)
  let T := ((30 + (3 / 2 : ℝ) * u) * (31 + (3 / 2 : ℝ) * u)) / 2 - 406
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hx1 : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ 1000000000).trans hx
  have hu : 0 ≤ u :=
    Real.log_nonneg
      ((le_div_iff₀ (by norm_num only : (0 : ℝ) < 1000000000)).mpr
        (by simpa only [one_mul] using hx))
  have hK : (K : ℝ) ≤ 30 + (3 / 2 : ℝ) * u := rootExponentCutoff_le_displacement hx
  have hk29 : 29 ≤ K := by
    apply
      (Nat.le_floor_iff
          (div_nonneg (Real.log_nonneg hx1) (Real.log_pos (by norm_num only : (1 : ℝ) < 2)).le)).mpr
    apply (le_div_iff₀ (Real.log_pos (by norm_num only : (1 : ℝ) < 2))).mpr
    have h :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 2 ^ (29 : ℕ))
        ((by norm_num only : (2 : ℝ) ^ (29 : ℕ) ≤ 1000000000).trans hx)
    rw [Real.log_pow] at h
    norm_num only at h
    exact h
  have hsum : (∑ k ∈ Finset.Icc 29 K, (k : ℝ)) ≤ T := by
    obtain ⟨t, he⟩ := Nat.exists_eq_add_of_le ((by norm_num only : 28 ≤ 29).trans hk29)
    have hs := sum_rootTail_exponents t
    rw [← he] at hs
    have hprod :=
      mul_le_mul hK (add_le_add hK (le_refl 1)) (add_nonneg (Nat.cast_nonneg K) zero_le_one)
        (show 0 ≤ 30 + (3 / 2 : ℝ) * u by linarith only [hu])
    rw [hs]
    unfold T
    have hc : (K : ℝ) = 28 + t := by exact_mod_cast he
    rw [← hc, show 29 + (t : ℝ) = (K : ℝ) + 1 by linarith only [hc]]
    nlinarith only [hprod]
  have hpoint (k : ℕ) (hk : k ∈ Finset.Icc 29 K) :
    (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20) ≤
      (21 / 20 : ℝ) * x ^ ((1 : ℝ) / 29) * k := by
    have hkcast : (29 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hr :=
      Real.rpow_le_rpow_of_exponent_le hx1
        (one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 29) hkcast)
    have hr1 : 1 ≤ x ^ ((1 : ℝ) / k) :=
      Real.one_le_rpow hx1 (div_nonneg zero_le_one (Nat.cast_nonneg k))
    have hsqrt : Real.sqrt (x ^ ((1 : ℝ) / k)) ≤ x ^ ((1 : ℝ) / k) :=
      Real.sqrt_le_iff.mpr ⟨zero_le_one.trans hr1, by nlinarith only [hr1]⟩
    have hm :=
      mul_le_mul_of_nonneg_left
        (show
          x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20 ≤
            (21 / 20 : ℝ) * x ^ ((1 : ℝ) / 29)
          by nlinarith only [hr, hsqrt])
        (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    nlinarith only [hm]
  have ht := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum] at ht
  have hcount :=
    mul_le_mul_of_nonneg_left hsum
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 21 / 20) (Real.rpow_nonneg hx0.le ((1 : ℝ) / 29)))
  have hxexp : x = 1000000000 * Real.exp u := by
    rw [Real.exp_log (div_pos hx0 (by norm_num only : (0 : ℝ) < 1000000000))]
    ring
  have hbroot : (1000000000 : ℝ) ^ ((1 : ℝ) / 29) ≤ 21 / 10 :=
    root_le_of_le_nat_pow (by norm_num only) (by norm_num only) (by norm_num only : 0 < 29)
      (by norm_num only)
  have hr : x ^ ((1 : ℝ) / 29) ≤ (21 / 10 : ℝ) * Real.exp (u / 29) := by
    rw [hxexp, Real.mul_rpow (by norm_num only) (Real.exp_pos u).le, ← Real.exp_mul]
    have h := mul_le_mul_of_nonneg_right hbroot (Real.exp_pos (u / 29)).le
    simpa only [mul_one_div] using h
  have hT : 0 ≤ T :=
    (Finset.sum_nonneg (s := Finset.Icc 29 K) fun k _ => (Nat.cast_nonneg k : (0 : ℝ) ≤ k)).trans
      hsum
  have hroot := mul_le_mul_of_nonneg_right hr hT
  have hpoly := mul_le_mul_of_nonneg_right (rootTailPolynomial_le_exp hu) (Real.exp_pos (u / 29)).le
  have hexp : Real.exp ((27 / 58 : ℝ) * u) * Real.exp (u / 29) = Real.exp (u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_assoc (220 : ℝ), hexp] at hpoly
  have hsqrt : Real.sqrt x = Real.sqrt (1000000000 : ℝ) * Real.exp (u / 2) := by
    rw [hxexp, Real.sqrt_eq_rpow, Real.mul_rpow (by norm_num only) (Real.exp_pos u).le, ←
      Real.exp_mul, Real.sqrt_eq_rpow]
    rw [mul_one_div]
  have hbase : (31600 : ℝ) ≤ Real.sqrt (1000000000 : ℝ) := Real.le_sqrt_of_sq_le (by norm_num only)
  have hlast := mul_le_mul_of_nonneg_right hbase (Real.exp_pos (u / 2)).le
  change
    (∑ k ∈ Finset.Icc 29 K, (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)) ≤
      (7 / 1000 : ℝ) * Real.sqrt x
  rw [hsqrt]
  change (21 / 20 : ℝ) * (21 / 10) * T * Real.exp (u / 29) ≤ 220 * Real.exp (u / 2) at hpoly
  nlinarith only [ht, hcount, hroot, hpoly, hlast, (Real.exp_pos (u / 2)).le]

end PseudoPrime.LLS.PaperStatements
