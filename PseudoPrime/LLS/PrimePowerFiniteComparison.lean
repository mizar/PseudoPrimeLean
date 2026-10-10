/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PrimePowerEvenComparison

/-! Finite exponent reindexing and prime-by-prime comparisons for LLS Lemma 5.1. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For an even natural exponent `k ≥ 2m`, reconstruct `k` as `2*(k/2-m+m)`.
The lower bound ensures natural subtraction does not truncate the half-index.
This identity recovers the original exponent when reindexing an even tail. -/
private theorem even_index_reconstruct {k m : ℕ} (hk : Even k) (hm : 2 * m ≤ k) :
    2 * (k / 2 - m + m) = k := by
  have hd : m ≤ k / 2 :=
    (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr (by simpa only [Nat.mul_comm] using hm)
  rw [Nat.sub_add_cancel hd]
  exact Nat.mul_div_cancel' hk.two_dvd

/-- Reindex a finite set of even exponents `k ≥ 2m` by `k/2-m`.
Reconstruction proves injectivity and preserves each summand. -/
theorem sum_even_reindex (s : Finset ℕ) (m : ℕ) (f : ℕ → ℝ) (he : ∀ k ∈ s, Even k)
    (hm : ∀ k ∈ s, 2 * m ≤ k) :
    ∑ k ∈ s, f k = ∑ j ∈ s.image (fun k ↦ k / 2 - m), f (2 * (j + m)) := by
  have hr : ∀ k ∈ s, 2 * (k / 2 - m + m) = k := fun k hk ↦
    even_index_reconstruct (he k hk) (hm k hk)
  have hi : Set.InjOn (fun k ↦ k / 2 - m) (↑s : Set ℕ) := by
    intro a ha b hb hab
    have h := congrArg (fun j ↦ 2 * (j + m)) hab
    simpa only [hr a ha, hr b hb] using h
  rw [Finset.sum_image hi]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hr k hk]

/-- For a finite set of even exponents `k ≥ 2m`, transfer a bound `B` on every
finite shifted sum whose reconstructed exponents lie in that set to the original sum.
Reindex by `k/2-m` and apply the assumed bound to its image; reconstruction preserves
membership. This applies uniform geometric-tail bounds to the actual even exponent set. -/
theorem sum_even_reindex_le (s : Finset ℕ) (m : ℕ) (f : ℕ → ℝ) (B : ℝ) (he : ∀ k ∈ s, Even k)
    (hm : ∀ k ∈ s, 2 * m ≤ k)
    (hb : ∀ t : Finset ℕ, (∀ j ∈ t, 2 * (j + m) ∈ s) → (∑ j ∈ t, f (2 * (j + m))) ≤ B) :
    (∑ k ∈ s, f k) ≤ B := by
  rw [sum_even_reindex s m f he hm]
  apply hb
  intro j hj
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
  rw [even_index_reconstruct (he k hk) (hm k hk)]
  exact hk

/-- For a norm-bounded complex value and nonnegative weights, the first term and
even terms bound the complete finite comparison from below.
The omitted odd terms are nonnegative. -/
theorem head_even_le_sum {z : ℂ} (hz : ‖z‖ ≤ 1) (s : Finset ℕ) (h1 : 1 ∈ s) (w : ℕ → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) :
    (1 + z.re) * w 1 + (∑ k ∈ (s.erase 1).filter Even, w k * ((z ^ k).re - (-1 : ℝ) ^ k)) ≤
      ∑ k ∈ s, w k * ((z ^ k).re - (-1 : ℝ) ^ k) := by
  classical
  have hs :
    (∑ k ∈ (s.erase 1).filter Even, w k * ((z ^ k).re - (-1 : ℝ) ^ k)) ≤
      ∑ k ∈ s.erase 1, w k * ((z ^ k).re - (-1 : ℝ) ^ k) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro k hk hn
    have he : ¬Even k := fun he ↦ hn (Finset.mem_filter.mpr ⟨hk, he⟩)
    exact
      mul_nonneg (hw k (Finset.mem_of_mem_erase hk))
        (Analysis.odd_power_difference_nonneg hz (Nat.not_even_iff_odd.mp he))
  have he := Finset.sum_erase_add s (fun k ↦ w k * ((z ^ k).re - (-1 : ℝ) ^ k)) h1
  simp only [pow_one, sub_neg_eq_add] at he
  nlinarith only [hs, he]

/-- For a prime `p ≥ 3`, `x ≥ 100`, and a unit-norm complex value, the finite
prime-power comparison is nonnegative whenever its positive exponents satisfy the cutoff and
include one. Reindex the even tail, apply its mass bound, and retain nonnegative odd terms. -/
theorem prime_odd_finite_comparison {x : ℝ} (hx : 100 ≤ x) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    {z : ℂ} (hz : ‖z‖ = 1) (s : Finset ℕ) (h1 : 1 ∈ s) (hcut : ∀ k ∈ s, 0 < k ∧ (p : ℝ) ^ k ≤ x) :
    0 ≤ ∑ k ∈ s, primePowerComparisonWeight x p k * ((z ^ k).re - (-1 : ℝ) ^ k) := by
  classical
  let e := (s.erase 1).filter Even
  have he : ∀ k ∈ e, Even k := fun k hk ↦ (Finset.mem_filter.mp hk).2
  have hm : ∀ k ∈ e, 2 * 1 ≤ k := by
    intro k hk
    have hs := (Finset.mem_filter.mp hk).1
    exact
      (Nat.two_le_iff k).mpr
        ⟨Nat.ne_of_gt (hcut k (Finset.mem_of_mem_erase hs)).1, (Finset.mem_erase.mp hs).1⟩
  have hw : ∀ k ∈ s, 0 ≤ primePowerComparisonWeight x p k := by
    intro k hk
    exact
      primePowerComparisonWeight_nonneg
        (one_lt_pow₀ (by exact_mod_cast hp.one_lt) (Nat.ne_of_gt (hcut k hk).1)) (hcut k hk).2
  have hr :=
    sum_even_reindex e 1 (fun k ↦ primePowerComparisonWeight x p k * ((z ^ k).re - (-1 : ℝ) ^ k)) he
      hm
  have hc : ∀ j ∈ e.image (fun k ↦ k / 2 - 1), (p : ℝ) ^ (2 * (j + 1)) ≤ x := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    rw [even_index_reconstruct (he k hk) (hm k hk)]
    exact (hcut k (Finset.mem_of_mem_erase (Finset.mem_filter.mp hk).1)).2
  have ht :=
    prime_odd_head_even_tail_nonneg_of_cutoff hx hp hp3
      (by simpa only [pow_one] using (hcut 1 h1).2) hz (e.image (fun k ↦ k / 2 - 1)) hc
  have hre : ∀ j : ℕ, (-1 : ℝ) ^ (2 * (j + 1)) = 1 := fun j ↦
    (show Even (2 * (j + 1)) from ⟨j + 1, by ring⟩).neg_one_pow
  simp only [hre] at hr
  rw [← hr] at ht
  exact le_trans ht (head_even_le_sum hz.le s h1 _ hw)

/-- For unit-norm complex `z` and arbitrary real weights, the comparison sum on
exponents one through five equals `(1 + Re z) * firstFiveComparisonPolynomial w (Re z)`.
Expand the finite interval and apply the unit-circle recurrence identity. This converts
the first-five part of the finite prime-two comparison to its certified polynomial. -/
theorem sum_first_five_difference {z : ℂ} (hz : ‖z‖ = 1) (w : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 5, w k * ((z ^ k).re - (-1 : ℝ) ^ k)) =
      (1 + z.re) * firstFiveComparisonPolynomial w z.re := by
  have hs : Finset.Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) := by decide
  rw [hs]
  rw [Finset.sum_insert (by decide : (1 : ℕ) ∉ {2, 3, 4, 5}),
    Finset.sum_insert (by decide : (2 : ℕ) ∉ {3, 4, 5}),
    Finset.sum_insert (by decide : (3 : ℕ) ∉ {4, 5}), Finset.sum_insert (by decide : (4 : ℕ) ∉ {5}),
    Finset.sum_singleton]
  have he := first_five_power_difference hz w
  norm_num only [pow_one, pow_succ, pow_zero, mul_one, one_mul, sub_neg_eq_add] at he ⊢
  unfold firstFiveComparisonPolynomial
  nlinarith only [he]

/-- For `x ≥ 100` and a unit-norm value, a finite prime-two comparison is nonnegative
if it contains the first five exponents and respects the cutoff. Combine the exact first-five
polynomial with the reindexed even tail; every omitted odd term is nonnegative. -/
theorem prime_two_finite_comparison {x : ℝ} (hx : 100 ≤ x) {z : ℂ} (hz : ‖z‖ = 1) (s : Finset ℕ)
    (hh : Finset.Icc 1 5 ⊆ s) (hcut : ∀ k ∈ s, 0 < k ∧ (2 : ℝ) ^ k ≤ x) :
    0 ≤ ∑ k ∈ s, primePowerComparisonWeight x 2 k * ((z ^ k).re - (-1 : ℝ) ^ k) := by
  classical
  let t := s \ Finset.Icc 1 5
  let e := t.filter Even
  have he : ∀ k ∈ e, Even k := fun k hk ↦ (Finset.mem_filter.mp hk).2
  have hm : ∀ k ∈ e, 2 * 3 ≤ k := by
    intro k hk
    have hs := Finset.mem_sdiff.mp (Finset.mem_filter.mp hk).1
    have hn : ¬k ≤ 5 := fun hn ↦ hs.2 (Finset.mem_Icc.mpr ⟨(hcut k hs.1).1, hn⟩)
    exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
  have hr :=
    sum_even_reindex e 3 (fun k ↦ primePowerComparisonWeight x 2 k * ((z ^ k).re - (-1 : ℝ) ^ k)) he
      hm
  have hc : ∀ j ∈ e.image (fun k ↦ k / 2 - 3), (2 : ℝ) ^ (2 * (j + 3)) ≤ x := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    rw [even_index_reconstruct (he k hk) (hm k hk)]
    exact (hcut k (Finset.mem_sdiff.mp (Finset.mem_filter.mp hk).1).1).2
  have ht := prime_two_head_even_tail_nonneg_of_cutoff hx hz (e.image (fun k ↦ k / 2 - 3)) hc
  have hre : ∀ j : ℕ, (-1 : ℝ) ^ (2 * (j + 3)) = 1 := fun j ↦
    (show Even (2 * (j + 3)) from ⟨j + 3, by ring⟩).neg_one_pow
  simp only [hre] at hr
  rw [← hr, ← sum_first_five_difference hz] at ht
  have hs :
    (∑ k ∈ e, primePowerComparisonWeight x 2 k * ((z ^ k).re - (-1 : ℝ) ^ k)) ≤
      ∑ k ∈ t, primePowerComparisonWeight x 2 k * ((z ^ k).re - (-1 : ℝ) ^ k) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro k hk hn
    have ho : Odd k := Nat.not_even_iff_odd.mp (fun he ↦ hn (Finset.mem_filter.mpr ⟨hk, he⟩))
    have hks := (Finset.mem_sdiff.mp hk).1
    exact
      mul_nonneg
        (primePowerComparisonWeight_nonneg
          (one_lt_pow₀ (by norm_num only : (1 : ℝ) < 2) (Nat.ne_of_gt (hcut k hks).1))
          (hcut k hks).2)
        (Analysis.odd_power_difference_nonneg hz.le ho)
  have hd :=
    Finset.sum_sdiff (f := fun k ↦ primePowerComparisonWeight x 2 k * ((z ^ k).re - (-1 : ℝ) ^ k))
      hh
  nlinarith only [ht, hs, hd]

/-- For a prime `p ≤ x`, `x ≥ 100`, and unit-norm complex `z`, the weighted
comparison on `1 ≤ k ≤ p.log (floor x)` is nonnegative. The cutoff bounds every power
by `x`. For `p = 2` it contains the first five exponents, allowing the polynomial and
even-tail bound; for `p ≥ 3` the first weight controls the even tail. This supplies the
nonzero character-value case of the prime-by-prime comparison. -/
theorem prime_unit_interval_comparison {x : ℝ} (hx : 100 ≤ x) {p : ℕ} (hp : p.Prime)
    (hpx : (p : ℝ) ≤ x) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤
      ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
        primePowerComparisonWeight x p k * ((z ^ k).re - (-1 : ℝ) ^ k) := by
  have hx1 : 1 ≤ x := le_trans (by norm_num only : (1 : ℝ) ≤ 100) hx
  have hf : ⌊x⌋₊ ≠ 0 := Nat.ne_of_gt (Nat.floor_pos.mpr hx1)
  have hc : ∀ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊), 0 < k ∧ (p : ℝ) ^ k ≤ x := by
    intro k hk
    have h := Finset.mem_Icc.mp hk
    exact
      ⟨h.1,
        (by exact_mod_cast Nat.pow_le_of_le_log hf h.2 : (p : ℝ) ^ k ≤ (⌊x⌋₊ : ℝ)).trans
          (Nat.floor_le (zero_le_one.trans hx1))⟩
  by_cases hp2 : p = 2
  · subst p
    apply prime_two_finite_comparison hx hz _ _ hc
    intro k hk
    exact
      Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hk).1,
          (Finset.mem_Icc.mp hk).2.trans
            (Nat.le_log_of_pow_le (by decide)
              (Nat.le_floor (le_trans (by norm_num only : ((2 ^ 5 : ℕ) : ℝ) ≤ 100) hx)))⟩
  · have hp3 : 3 ≤ p := Nat.succ_le_of_lt (lt_of_le_of_ne hp.two_le (Ne.symm hp2))
    exact
      prime_odd_finite_comparison hx hp hp3 hz _
        (Finset.mem_Icc.mpr
          ⟨le_rfl, Nat.le_log_of_pow_le hp.one_lt (by simpa only [pow_one] using Nat.le_floor hpx)⟩)
        hc

/-- A decreasing weight sequence nonnegative through `K` has a nonpositive alternating sum
starting at exponent one. Pair consecutive terms by two-step induction. -/
private theorem alternating_weight_sum_nonpos (w : ℕ → ℝ) (hm : ∀ k : ℕ, 0 < k → w (k + 1) ≤ w k)
    (K : ℕ) (hw : ∀ k ∈ Finset.Icc 1 K, 0 ≤ w k) :
    (∑ k ∈ Finset.Icc 1 K, w k * (-1 : ℝ) ^ k) ≤ 0 := by
  induction K using Nat.twoStepInduction with
  | zero => rw [show Finset.Icc 1 0 = ∅ from rfl, Finset.sum_empty]
  | one =>
    simpa only [Finset.Icc_self, Finset.sum_singleton, pow_one, mul_neg_one] using
      neg_nonpos.mpr (hw 1 (Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩))
  | more n ih ih' =>
    have hpos : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    rw [show n + 2 = (n + 1) + 1 by rfl,
      Finset.sum_Icc_succ_top (Nat.le_trans hpos (Nat.le_succ (n + 1)))]
    rcases Nat.even_or_odd (n + 2) with he | ho
    · have he' : Odd (n + 1) := by
        exact Nat.not_even_iff_odd.mp (fun h ↦ (Nat.not_even_iff_odd.mpr h.add_one) he)
      rw [Finset.sum_Icc_succ_top hpos, he.neg_one_pow, he'.neg_one_pow, mul_one, mul_neg_one]
      have hi :=
        ih
          (fun k hk ↦
            hw k
              (Finset.mem_Icc.mpr
                ⟨(Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2.trans (Nat.le_add_right n 2)⟩))
      have hd := hm (n + 1) (Nat.succ_pos n)
      linarith only [hi, hd]
    · rw [ho.neg_one_pow, mul_neg_one]
      have hi :=
        ih'
          (fun k hk ↦
            hw k
              (Finset.mem_Icc.mpr
                ⟨(Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2.trans (Nat.le_succ (n + 1))⟩))
      have hn := hw (n + 2) (Finset.mem_Icc.mpr ⟨hpos.trans (Nat.le_succ (n + 1)), le_rfl⟩)
      linarith only [hi, hn]

/-- For a prime and a positive exponent, the comparison weight decreases with the exponent.
The correction cancels, leaving the reciprocal of an increasing positive denominator. -/
theorem primePowerComparisonWeight_succ_le (x : ℝ) {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    primePowerComparisonWeight x p (k + 1) ≤ primePowerComparisonWeight x p k := by
  rw [primePowerComparisonWeight_eq hp (Nat.succ_ne_zero k),
    primePowerComparisonWeight_eq hp (Nat.ne_of_gt hk)]
  apply sub_le_sub_right
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hpk : (1 : ℝ) ≤ p := (by exact_mod_cast hp.one_lt : (1 : ℝ) < p).le
  apply one_div_le_one_div_of_le (mul_pos hk0 (pow_pos hp0 k))
  exact
    mul_le_mul (by exact_mod_cast Nat.le_succ k) (pow_le_pow_right₀ hpk (Nat.le_succ k))
      (pow_nonneg hp0.le k) (by exact_mod_cast (Nat.zero_le (k + 1)))

/-- For a prime `p` and real `x ≥ 1`, the alternating weighted sum over
`1 ≤ k ≤ p.log (floor x)` is nonpositive. The weights decrease with the positive exponent
and are nonnegative on the cutoff interval; pairing successive terms proves the bound.
This handles primes where the character value vanishes, including an empty interval. -/
theorem prime_alternating_sum_nonpos {x : ℝ} (hx : 1 ≤ x) {p : ℕ} (hp : p.Prime) :
    (∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊), primePowerComparisonWeight x p k * (-1 : ℝ) ^ k) ≤ 0 := by
  exact
    alternating_weight_sum_nonpos _ (fun k hk ↦ primePowerComparisonWeight_succ_le x hp hk) _
      (fun _ hk ↦ primePowerComparisonWeight_nonneg_Icc hx hp hk)

/-- For any complex Dirichlet character modulo a nonzero modulus, a prime
`p ≤ x`, and `x ≥ 100`, its weighted real character sum on the prime-power cutoff is at
least the alternating weighted sum. A nonzero value has unit norm and uses the unit-circle
comparison; a zero value makes all positive powers vanish and uses the nonpositive
alternating sum. No quadratic, primitive, or GRH assumption is needed for Lemma 5.1. -/
theorem prime_character_interval_comparison {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 100 ≤ x) {p : ℕ} (hp : p.Prime) (hpx : (p : ℝ) ≤ x) :
    (∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊), primePowerComparisonWeight x p k * (-1 : ℝ) ^ k) ≤
      ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊), primePowerComparisonWeight x p k * (χ (p ^ k)).re := by
  by_cases hc : χ p = 0
  · have hz : ∀ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊), (χ (p ^ k)).re = 0 := by
      intro k hk
      rw [map_pow, hc, zero_pow (Nat.ne_of_gt (Finset.mem_Icc.mp hk).1)]
      rfl
    have hs :
      (∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊), primePowerComparisonWeight x p k * (χ (p ^ k)).re) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [hz k hk, mul_zero]
    rw [hs]
    exact prime_alternating_sum_nonpos (le_trans (by norm_num only : (1 : ℝ) ≤ 100) hx) hp
  · have h := prime_unit_interval_comparison hx hp hpx (character_norm_one_of_ne_zero χ hc)
    simpa only [Nat.cast_pow, map_pow, mul_sub, Finset.sum_sub_distrib, sub_nonneg] using h

/-- For a complex Dirichlet character modulo a nonzero modulus and any real
`x`, rewrite the real part of the character-weighted Mangoldt sum on `0 < n ≤ floor x`
as the sum over primes `p ≤ floor x` and exponents `1 ≤ k ≤ p.log (floor x)` with the
same comparison weights. Mangoldt vanishes off prime powers, and unique prime-power
reindexing preserves each summand. This finite algebraic identity requires no positivity
or analytic hypotheses and lets the prime-by-prime inequalities prove Lemma 5.1. -/
theorem character_log_sum_eq_primePower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
          χ n *
            (ArithmeticFunction.vonMangoldt n *
                (1 / ((n : ℝ) * Real.log n) - 1 / (x * Real.log x)) :
              ℝ)).re =
      ∑ p ∈ Nat.primesLE ⌊x⌋₊,
        ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊), primePowerComparisonWeight x p k * (χ (p ^ k)).re := by
  classical
  rw [Complex.re_sum, ← Finset.Icc_add_one_left_eq_Ioc]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  let f : ℕ → ℝ := fun n ↦
    (χ n).re *
      (ArithmeticFunction.vonMangoldt n * (1 / ((n : ℝ) * Real.log n) - 1 / (x * Real.log x)))
  have hf : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with IsPrimePow n, f n) = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n := by
    apply Finset.sum_filter_of_ne
    intro n _ hn
    by_contra hp
    have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp
    exact
      hn
        (by
          dsimp only [f]; rw [hz, zero_mul, mul_zero])
  change (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) = _
  rw [← hf, AnalyticNumberTheory.Arithmetic.sum_primePow_eq_sum_primesLE]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro k _
  simp only [f, primePowerComparisonWeight, Nat.cast_pow]
  ring

/-- For any complex Dirichlet character of nonzero modulus and x ≥ 100, the alternating
prime-power sum is bounded above by the real character-weighted comparison sum. Reindex
Mangoldt support by prime powers and apply the prime-wise finite comparison.
This is the arithmetic proof shared by Lemma 5.1 and the logarithmic lower bound. -/
theorem character_primePower_comparison_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 100 ≤ x) :
    alternatingPrimePowerSum x ≤
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
          χ n *
            (ArithmeticFunction.vonMangoldt n *
                (1 / ((n : ℝ) * Real.log n) - 1 / (x * Real.log x)) :
              ℝ)).re := by
  rw [character_log_sum_eq_primePower]
  unfold alternatingPrimePowerSum
  apply Finset.sum_le_sum
  intro p hp
  have h := Nat.mem_primesLE.mp hp
  have hc :=
    prime_character_interval_comparison χ hx h.2
      ((by exact_mod_cast h.1 : (p : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans
        (Nat.floor_le (le_trans (by norm_num only : (0 : ℝ) ≤ 100) hx)))
  convert hc using 1
  apply Finset.sum_congr rfl
  intro k _
  unfold primePowerComparisonWeight
  ring

end PseudoPrime.LLS.PaperStatements
