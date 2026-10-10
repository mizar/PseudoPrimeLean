/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CosetRootTail
public import PseudoPrime.LLS.CosetNormAverage

/-! # Uniform composite root sums for the coset prime criterion

The quadratic slice, fixed prefix and variable tail together give the
uniform factor `11/5` above cutoff one billion.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For cutoff at least one billion, the exponent-two root slice is at most
`2001 sqrt x/1000`. The inner square root is at most `sqrt x/100`, because
`sqrt x` is at least ten thousand. This controls the leading composite slice. -/
theorem quadraticRootSlice_le {x : ℝ} (hx : 1000000000 ≤ x) :
    (2 : ℝ) * (x ^ ((1 : ℝ) / 2) + Real.sqrt (x ^ ((1 : ℝ) / 2)) / 20) ≤
      (2001 / 1000 : ℝ) * Real.sqrt x := by
  rw [← Real.sqrt_eq_rpow]
  have hb : (10000 : ℝ) ≤ Real.sqrt x :=
    Real.le_sqrt_of_sq_le ((by norm_num only : (10000 : ℝ) ^ 2 ≤ 1000000000).trans hx)
  have hs : Real.sqrt (Real.sqrt x) ≤ Real.sqrt x / 100 :=
    Real.sqrt_le_iff.mpr
      ⟨div_nonneg (Real.sqrt_nonneg x) (by norm_num only), by nlinarith only [hb]⟩
  linarith only [hs]

/-- For cutoff at least one billion, the full composite root majorant is
at most `11 sqrt x/5`. Split at exponents two and twenty-nine, then combine
the certified quadratic, fixed-prefix and tail bounds. This eliminates the
finite root sum from the coset prime criterion. -/
theorem compositeRootSum_le {x : ℝ} (hx : 1000000000 ≤ x) :
    (∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊,
        (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)) ≤
      (11 / 5 : ℝ) * Real.sqrt x := by
  let K := ⌊Real.log x / Real.log 2⌋₊
  let f := fun k : ℕ => (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)
  have hx1 : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ 1000000000).trans hx
  have hK : 29 ≤ K := by
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
  have hsplit :=
    Finset.sum_Ico_consecutive f (m := 2) (n := 29) (k := K + 1) (by norm_num only)
      (Nat.le_add_right K 1 |>.trans' hK)
  change
    (∑ i ∈ Finset.Ico 2 (28 + 1), f i) + (∑ i ∈ Finset.Ico 29 (K + 1), f i) =
      ∑ i ∈ Finset.Ico 2 (K + 1), f i at hsplit
  rw [Finset.Ico_add_one_right_eq_Icc 2 28, Finset.Ico_add_one_right_eq_Icc 29 K,
    Finset.Ico_add_one_right_eq_Icc 2 K] at hsplit
  have hhead :=
    Finset.sum_Ico_consecutive f (m := 2) (n := 3) (k := 29) (by norm_num only) (by norm_num only)
  change
    (∑ i ∈ Finset.Ico 2 (2 + 1), f i) + (∑ i ∈ Finset.Ico 3 (28 + 1), f i) =
      ∑ i ∈ Finset.Ico 2 (28 + 1), f i at hhead
  rw [Finset.Ico_add_one_right_eq_Icc 2 2, Finset.Ico_add_one_right_eq_Icc 3 28,
    Finset.Ico_add_one_right_eq_Icc 2 28] at hhead
  simp only [Finset.Icc_self, Finset.sum_singleton] at hhead
  have htwo := quadraticRootSlice_le hx
  have hprefix := smallRootPrefix_le_sqrt_fraction hx
  have htail := rootTail_le_sqrt_fraction hx
  change (∑ k ∈ Finset.Icc 2 K, f k) ≤ (11 / 5 : ℝ) * Real.sqrt x
  change f 2 ≤ (2001 / 1000 : ℝ) * Real.sqrt x at htwo
  change (∑ k ∈ Finset.Icc 3 28, f k) ≤ (19 / 100 : ℝ) * Real.sqrt x at hprefix
  change (∑ k ∈ Finset.Icc 29 K, f k) ≤ (7 / 1000 : ℝ) * Real.sqrt x at htail
  linarith only [hsplit, hhead, htwo, hprefix, htail, Real.sqrt_nonneg x]

/-- Under GRH, modulus at least twenty thousand and cutoff at least one
billion, the explicit principal lower bound exceeding the nonprincipal
majorant plus `11 index(H) sqrt x/5` yields the least prime in any coset.
The uniform composite estimate removes the exponent sum from the criterion. -/
theorem exists_least_prime_in_coset_le_of_explicit_gap {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (a : (ZMod q)ˣ) (hq : 20000 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 1000000000 ≤ x)
    (hgap :
      (H.index : ℝ) * ((11 / 5 : ℝ) * Real.sqrt x) + cosetNonprincipalUpper q H x <
        cosetPrincipalLower q x) :
    ∃ p : ℕ, IsLeast (primesInCoset q H a) p ∧ (p : ℝ) ≤ x := by
  have hc :=
    mul_le_mul_of_nonneg_left (compositeRootSum_le hx) (Nat.cast_nonneg H.index : (0 : ℝ) ≤ H.index)
  apply
    exists_least_prime_in_coset_le_of_explicit_root_gap H a
      ((by norm_num only : (64 : ℕ) ≤ 20000).trans hq) hGRH
      ((by norm_num only : (65536 : ℝ) ≤ 1000000000).trans hx)
  exact lt_of_le_of_lt (add_le_add hc (le_refl _)) hgap

end PseudoPrime.LLS.PaperStatements
