/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.MixedFourierBandBudget

/-! # Geometric bounds for dyadic fourth-moment bands -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A finite geometric sum with ratio at most three quarters is at most four.

Input: A nonnegative real ratio `r ≤ 3/4` and a finite range length.
Claim: The sum of the first `n` powers of `r` is at most `4`.
Proof: Compare termwise with powers of `3/4` and use the exact geometric
identity.
Role: Bounds the increasing square-root part of the dyadic split. -/
theorem geom_power_sum_le_four {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 3 / 4) (n : ℕ) :
    (∑ i ∈ Finset.range n, r ^ i) ≤ 4 := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, (3 / 4 : ℝ) ^ i := by
      apply Finset.sum_le_sum
      intro i hi
      exact pow_le_pow_left₀ hr0 hr i
    _ ≤ 4 := by
      have hgeom := geom_sum_mul_add (-(1 / 4 : ℝ)) n
      have hratio : -(1 / 4 : ℝ) + 1 = 3 / 4 := by norm_num only
      rw [hratio] at hgeom
      have hp : 0 ≤ (3 / 4 : ℝ) ^ n := pow_nonneg (by norm_num only : (0 : ℝ) ≤ 3 / 4) n
      nlinarith only [hgeom, hp]

/-- A finite geometric sum with ratio at most six sevenths is at most seven.

Input: A nonnegative real ratio `r ≤ 6/7` and a finite range length.
Claim: The sum of the first `n` powers of `r` is at most `7`.
Proof: Compare termwise with powers of `6/7` and use the exact geometric
identity.
Role: Bounds the decreasing inverse-fourth-root part of the dyadic split. -/
theorem geom_power_sum_le_seven {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 6 / 7) (n : ℕ) :
    (∑ i ∈ Finset.range n, r ^ i) ≤ 7 := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, (6 / 7 : ℝ) ^ i := by
      apply Finset.sum_le_sum
      intro i hi
      exact pow_le_pow_left₀ hr0 hr i
    _ ≤ 7 := by
      have hgeom := geom_sum_mul_add (-(1 / 7 : ℝ)) n
      have hratio : -(1 / 7 : ℝ) + 1 = 6 / 7 := by norm_num only
      rw [hratio] at hgeom
      have hp : 0 ≤ (6 / 7 : ℝ) ^ n := pow_nonneg (by norm_num only : (0 : ℝ) ≤ 6 / 7) n
      nlinarith only [hgeom, hp]

/-- Square roots commute with natural powers of two.

Input: A natural exponent `j`.
Claim: `sqrt(2^j) = sqrt(2)^j`.
Proof: Induct on `j` and use multiplicativity of `sqrt` on nonnegative
factors.
Role: Expresses the lower dyadic sum as a geometric progression. -/
theorem sqrt_two_pow (j : ℕ) : Real.sqrt ((2 : ℝ) ^ j) = (Real.sqrt 2) ^ j := by
  induction j with
  | zero => simp only [pow_zero, Real.sqrt_one]
  | succ j ih =>
    rw [pow_succ, Real.sqrt_mul (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) j)]
    rw [ih, pow_succ]

/-- Fourth roots commute with natural powers of two.

Input: A natural exponent `j`.
Claim: `sqrt(sqrt(2^j)) = sqrt(sqrt 2)^j`.
Proof: Apply the square-root product identity twice in an induction.
Role: Expresses the upper dyadic tail as an inverse geometric progression. -/
theorem fourthRoot_two_pow (j : ℕ) :
    Real.sqrt (Real.sqrt ((2 : ℝ) ^ j)) = (Real.sqrt (Real.sqrt 2)) ^ j := by
  induction j with
  | zero => simp only [pow_zero, Real.sqrt_one]
  | succ j ih =>
    rw [pow_succ]
    rw [Real.sqrt_mul (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) j)]
    rw [Real.sqrt_mul (Real.sqrt_nonneg _) (Real.sqrt 2)]
    rw [ih, pow_succ]

/-- Sum square roots of dyadic scales through the last scale.

Input: A natural terminal index `m`.
Claim: `sum_{j≤m} sqrt(2^j) ≤ 4 sqrt(2^m)`.
Proof: Express the summands as powers of `sqrt 2` and induct using
`sqrt 2 ≥ 4/3`.
Role: Bounds the lower-index portion of a split dyadic sum. -/
theorem sum_sqrt_two_powers_le (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), Real.sqrt ((2 : ℝ) ^ j)) ≤ 4 * Real.sqrt ((2 : ℝ) ^ m) := by
  simp only [sqrt_two_pow]
  have hq : 4 / 3 ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num only)
  have hs : (∑ j ∈ Finset.range (m + 1), (Real.sqrt 2) ^ j) ≤ 4 * (Real.sqrt 2) ^ m := by
    induction m with
    | zero =>
      simp only [pow_zero, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num only
    | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hq0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      have hp := pow_nonneg hq0 m
      have hm := mul_le_mul_of_nonneg_right hq hp
      nlinarith only [ih, hm]
  exact hs

/-- Sum inverse fourth roots across a finite dyadic tail.

Input: A starting index `m` and an arbitrary finite endpoint `n`.
Claim: The sum over `m ≤ j < n` of `2^{-j/4}` is at most seven times
`2^{-m/4}`.
Proof: Reindex the interval by `j=m+k`; the ratio is at most `6/7` because
`2^{1/4} ≥ 7/6`.
Role: Bounds the upper-index portion without a factor for the number of bands. -/
theorem sum_inv_fourthRoot_two_powers_Ico_le_seven (m n : ℕ) :
    (∑ j ∈ Finset.Ico m n, (Real.sqrt (Real.sqrt ((2 : ℝ) ^ j)))⁻¹) ≤
      7 * (Real.sqrt (Real.sqrt ((2 : ℝ) ^ m)))⁻¹ := by
  let q : ℝ := Real.sqrt (Real.sqrt 2)
  have hq : 7 / 6 ≤ q := by
    dsimp only [q]
    apply Real.le_sqrt_of_sq_le
    apply Real.le_sqrt_of_sq_le
    norm_num only
  have hqpos : 0 < q := by
    have hq0 : (0 : ℝ) < 7 / 6 := by norm_num only
    exact lt_of_lt_of_le hq0 hq
  have hr : q⁻¹ ≤ 6 / 7 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hqpos).mpr
    have hm := mul_le_mul_of_nonneg_right hq (by norm_num only : (0 : ℝ) ≤ 6 / 7)
    nlinarith only [hm]
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [fourthRoot_two_pow]
  change (∑ k ∈ Finset.range (n - m), (q ^ (m + k))⁻¹) ≤ 7 * (q ^ m)⁻¹
  calc
    _ = q⁻¹ ^ m * ∑ k ∈ Finset.range (n - m), q⁻¹ ^ k := by
      calc
        _ = ∑ k ∈ Finset.range (n - m), q⁻¹ ^ (m + k) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [← inv_pow]
        _ = ∑ k ∈ Finset.range (n - m), q⁻¹ ^ m * q⁻¹ ^ k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [pow_add]
        _ = _ := by rw [← Finset.mul_sum]
    _ ≤ q⁻¹ ^ m * 7 := by
      exact
        mul_le_mul_of_nonneg_left (geom_power_sum_le_seven (inv_nonneg.mpr hqpos.le) hr _)
          (pow_nonneg (inv_nonneg.mpr hqpos.le) _)
    _ = _ := by ring

/-- The fourth power of a fourth-root expression returns its argument.

Input: A nonnegative real `x`.
Claim: `(sqrt(sqrt x))^4 = x`.
Proof: Apply the square-root square identity twice.
Role: Enables fourth-power comparisons without fractional exponents. -/
theorem quarterRoot_fourth_pow {x : ℝ} (hx : 0 ≤ x) : (Real.sqrt (Real.sqrt x)) ^ 4 = x := by
  rw [show 4 = 2 * 2 by norm_num only, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hx]

/-- The fourth power of a square root returns the square of its argument.

Input: A nonnegative real `x`.
Claim: `(sqrt x)^4 = x^2`.
Proof: Apply the square-root square identity once and unfold the fourth power.
Role: Supplies the denominator identity in the cubic-budget comparison. -/
theorem sqrt_fourth_pow {x : ℝ} (hx : 0 ≤ x) : (Real.sqrt x) ^ 4 = x ^ 2 := by
  rw [show 4 = 2 * 2 by norm_num only, pow_mul, Real.sq_sqrt hx]

/-- A quadratic band budget gives the increasing fourth-root envelope.

Input: Nonnegative `A`, `K`, and `E` with `A*K^2 ≤ E`.
Claim: `K^2*A^(3/4) ≤ E^(3/4)*sqrt K`, with quarter powers represented
by nested square roots.
Proof: Cube the budget, multiply by `K^2`, and compare fourth powers.
Role: Supplies the lower-side term in the dyadic split. -/
theorem dyadicQuarter_low_bound {A K E : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hAK : A * K ^ 2 ≤ E) :
    K ^ 2 * (Real.sqrt (Real.sqrt A)) ^ 3 ≤ (Real.sqrt (Real.sqrt E)) ^ 3 * Real.sqrt K := by
  have hbudget3 := pow_le_pow_left₀ (mul_nonneg hA (sq_nonneg K)) hAK 3
  have hbudget := mul_le_mul_of_nonneg_right hbudget3 (sq_nonneg K)
  have hleft4 : (K ^ 2 * (Real.sqrt (Real.sqrt A)) ^ 3) ^ 4 = K ^ 8 * A ^ 3 := by
    rw [mul_pow]
    calc
      _ = K ^ 8 * ((Real.sqrt (Real.sqrt A)) ^ 4) ^ 3 := by ring
      _ = _ := by rw [quarterRoot_fourth_pow hA]
  have hright4 : ((Real.sqrt (Real.sqrt E)) ^ 3 * Real.sqrt K) ^ 4 = E ^ 3 * K ^ 2 := by
    rw [mul_pow]
    calc
      _ = ((Real.sqrt (Real.sqrt E)) ^ 4) ^ 3 * (Real.sqrt K) ^ 4 := by ring
      _ = _ := by rw [quarterRoot_fourth_pow hE, sqrt_fourth_pow hK]
  have hpow : K ^ 8 * A ^ 3 ≤ E ^ 3 * K ^ 2 := by
    calc
      _ = (A * K ^ 2) ^ 3 * K ^ 2 := by ring
      _ ≤ _ := hbudget
  apply
    le_of_pow_le_pow_left₀ (by decide : 4 ≠ 0)
      (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) 3) (Real.sqrt_nonneg _))
  rw [hleft4, hright4]
  exact hpow

/-- A cubic band budget gives the decreasing fourth-root envelope.

Input: Nonnegative `A`, `C`, and `P`, positive `K`, and `A*K^3 ≤ C*P^3`.
Claim: `K^2*A^(3/4) ≤ (C*P^3)^(3/4)/K^(1/4)`.
Proof: Cube the budget, divide by `K`, and compare fourth powers.
Role: Supplies the upper-side term in the dyadic split. -/
theorem dyadicQuarter_cubic_bound {A K C P : ℝ} (hA : 0 ≤ A) (hK : 0 < K) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hAK : A * K ^ 3 ≤ C * P ^ 3) :
    K ^ 2 * (Real.sqrt (Real.sqrt A)) ^ 3 ≤
      (Real.sqrt (Real.sqrt (C * P ^ 3))) ^ 3 * (Real.sqrt (Real.sqrt K))⁻¹ := by
  have hAK3 := pow_le_pow_left₀ (mul_nonneg hA (pow_nonneg hK.le 3)) hAK 3
  have hdiv := div_le_div_of_nonneg_right hAK3 (le_of_lt hK)
  have hleft4 : (K ^ 2 * (Real.sqrt (Real.sqrt A)) ^ 3) ^ 4 = K ^ 8 * A ^ 3 := by
    rw [mul_pow]
    calc
      _ = K ^ 8 * ((Real.sqrt (Real.sqrt A)) ^ 4) ^ 3 := by ring
      _ = _ := by rw [quarterRoot_fourth_pow hA]
  have hright4 :
    ((Real.sqrt (Real.sqrt (C * P ^ 3))) ^ 3 * (Real.sqrt (Real.sqrt K))⁻¹) ^ 4 =
      (C * P ^ 3) ^ 3 / K := by
    rw [mul_pow]
    calc
      _ = ((Real.sqrt (Real.sqrt (C * P ^ 3))) ^ 4) ^ 3 / (Real.sqrt (Real.sqrt K)) ^ 4 := by
        rw [inv_pow]; ring
      _ = _ := by
        rw [quarterRoot_fourth_pow (mul_nonneg hC (pow_nonneg hP 3)), quarterRoot_fourth_pow hK.le]
  have hpow : K ^ 8 * A ^ 3 ≤ (C * P ^ 3) ^ 3 / K := by
    calc
      _ = (A * K ^ 3) ^ 3 / K := by field_simp [ne_of_gt hK]
      _ ≤ _ := hdiv
  apply
    le_of_pow_le_pow_left₀ (by decide : 4 ≠ 0)
      (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) 3) (inv_nonneg.mpr (Real.sqrt_nonneg _)))
  rw [hleft4, hright4]
  exact hpow

/-- Sum two complementary dyadic envelopes without a band-count factor.

Input: Bounds for `F j` by `A*sqrt(2^j)` through `m` and by
`B/(2^j)^(1/4)` above `m`, with `A,B ≥ 0`.
Claim: The sum through any finite endpoint is at most
`4*A*sqrt(2^m) + 7*B/(2^(m+1))^(1/4)`.
Proof: Split the finite sum at `m`, enlarge each index set, and apply the
two geometric estimates.
Role: Removes the logarithmic number of dyadic bands from the error sum. -/
theorem sum_split_by_dyadic_cutoff {n m : ℕ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (F : ℕ → ℝ)
    (hlo : ∀ j, j ≤ m → F j ≤ A * Real.sqrt ((2 : ℝ) ^ j))
    (hhi : ∀ j, m < j → F j ≤ B * (Real.sqrt (Real.sqrt ((2 : ℝ) ^ j)))⁻¹) :
    (∑ j ∈ Finset.range (n + 1), F j) ≤
      4 * A * Real.sqrt ((2 : ℝ) ^ m) + 7 * B * (Real.sqrt (Real.sqrt ((2 : ℝ) ^ (m + 1))))⁻¹ := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1)) (fun j ↦ j ≤ m) F
  simp only [not_le] at hsplit
  rw [← hsplit]
  have hlow : (∑ j ∈ Finset.range (n + 1) with j ≤ m, F j) ≤ 4 * A * Real.sqrt ((2 : ℝ) ^ m) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1) with j ≤ m, A * Real.sqrt ((2 : ℝ) ^ j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hlo j (Finset.mem_filter.mp hj).2
      _ ≤ ∑ j ∈ Finset.range (m + 1), A * Real.sqrt ((2 : ℝ) ^ j) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          have hmj := (Finset.mem_filter.mp hj).2
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le hmj)
        · intro j hj hnot
          exact mul_nonneg hA (Real.sqrt_nonneg _)
      _ = A * ∑ j ∈ Finset.range (m + 1), Real.sqrt ((2 : ℝ) ^ j) := by rw [← Finset.mul_sum]
      _ ≤ A * (4 * Real.sqrt ((2 : ℝ) ^ m)) :=
        mul_le_mul_of_nonneg_left (sum_sqrt_two_powers_le m) hA
      _ = _ := by ring
  have hhigh :
    (∑ j ∈ Finset.range (n + 1) with m < j, F j) ≤
      7 * B * (Real.sqrt (Real.sqrt ((2 : ℝ) ^ (m + 1))))⁻¹ := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1) with m < j, B * (Real.sqrt (Real.sqrt ((2 : ℝ) ^ j)))⁻¹ := by
        apply Finset.sum_le_sum
        intro j hj
        exact hhi j (Finset.mem_filter.mp hj).2
      _ ≤ ∑ j ∈ Finset.Ico (m + 1) (n + 1), B * (Real.sqrt (Real.sqrt ((2 : ℝ) ^ j)))⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          have hmem := Finset.mem_filter.mp hj
          exact Finset.mem_Ico.mpr ⟨Nat.succ_le_of_lt hmem.2, Finset.mem_range.mp hmem.1⟩
        · intro j hj hnot
          exact mul_nonneg hB (inv_nonneg.mpr (Real.sqrt_nonneg _))
      _ = B * ∑ j ∈ Finset.Ico (m + 1) (n + 1), (Real.sqrt (Real.sqrt ((2 : ℝ) ^ j)))⁻¹ := by
        rw [← Finset.mul_sum]
      _ ≤ B * (7 * (Real.sqrt (Real.sqrt ((2 : ℝ) ^ (m + 1))))⁻¹) :=
        mul_le_mul_of_nonneg_left (sum_inv_fourthRoot_two_powers_Ico_le_seven (m + 1) (n + 1)) hB
      _ = _ := by ring
  exact add_le_add hlow hhigh

/-- Express the split bound using any real cutoff between consecutive scales.

Input: A nonnegative cutoff `H` with `2^m ≤ H < 2^(m+1)` and the two
pointwise dyadic envelopes.
Claim: The finite sum is at most `4*A*sqrt(H) + 7*B/(H^(1/4))`.
Proof: Apply the discrete split bound and monotonicity of square roots and
their positive reciprocals.
Role: Lets the energy and cubic budgets choose the balancing scale. -/
theorem sum_split_by_real_cutoff {n m : ℕ} {A B H : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlo : (2 : ℝ) ^ m ≤ H) (hhi : H < (2 : ℝ) ^ (m + 1)) (F : ℕ → ℝ)
    (hFLo : ∀ j, j ≤ m → F j ≤ A * Real.sqrt ((2 : ℝ) ^ j))
    (hFHi : ∀ j, m < j → F j ≤ B * (Real.sqrt (Real.sqrt ((2 : ℝ) ^ j)))⁻¹) :
    (∑ j ∈ Finset.range (n + 1), F j) ≤
      4 * A * Real.sqrt H + 7 * B * (Real.sqrt (Real.sqrt H))⁻¹ := by
  have hbase := sum_split_by_dyadic_cutoff (n := n) (m := m) hA hB F hFLo hFHi
  have hHpos : 0 < H := lt_of_lt_of_le (pow_pos (by norm_num only : (0 : ℝ) < 2) m) hlo
  have hroot : Real.sqrt (Real.sqrt H) ≤ Real.sqrt (Real.sqrt ((2 : ℝ) ^ (m + 1))) :=
    Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hhi.le)
  have hrootpos : 0 < Real.sqrt (Real.sqrt H) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hHpos)
  have hinv : (Real.sqrt (Real.sqrt ((2 : ℝ) ^ (m + 1))))⁻¹ ≤ (Real.sqrt (Real.sqrt H))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hrootpos hroot
  calc
    _ ≤ 4 * A * Real.sqrt ((2 : ℝ) ^ m) + 7 * B * (Real.sqrt (Real.sqrt ((2 : ℝ) ^ (m + 1))))⁻¹ :=
      hbase
    _ ≤ _ :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlo) (by positivity))
        (mul_le_mul_of_nonneg_left hinv (by positivity))

/-- Every real cutoff at least one lies between consecutive powers of two.

Input: A real number `H` with `1 ≤ H`.
Claim: There is a natural index `m` with `2^m ≤ H < 2^(m+1)`.
Proof: Take `m = Nat.log2 (Nat.floor H)` and use the floor and logarithm bounds.
Role: Chooses the balancing band for the energy and cubic budgets. -/
theorem exists_nat_pow_two_cutoff {H : ℝ} (hH : (1 : ℝ) ≤ H) :
    ∃ m : ℕ, (2 : ℝ) ^ m ≤ H ∧ H < (2 : ℝ) ^ (m + 1) := by
  refine ⟨Nat.log2 (Nat.floor H), ?_, ?_⟩
  · have hH0 : (0 : ℝ) ≤ H := by linarith only [hH]
    have hfloor_one : 1 ≤ Nat.floor H :=
      (Nat.le_floor_iff hH0).mpr (by simpa only [Nat.cast_one] using hH)
    have hfloor_pos : 0 < Nat.floor H :=
      Nat.lt_of_lt_of_le (by norm_num only : (0 : ℕ) < 1) hfloor_one
    have hlog : 2 ^ Nat.log2 (Nat.floor H) ≤ Nat.floor H := Nat.log2_self_le hfloor_pos.ne'
    have hlog_real : ((2 ^ Nat.log2 (Nat.floor H) : ℕ) : ℝ) ≤ Nat.floor H := by exact_mod_cast hlog
    have hfloor : (Nat.floor H : ℝ) ≤ H := Nat.floor_le hH0
    calc
      (2 : ℝ) ^ Nat.log2 (Nat.floor H) = ((2 ^ Nat.log2 (Nat.floor H) : ℕ) : ℝ) := by norm_cast
      _ ≤ (Nat.floor H : ℝ) := hlog_real
      _ ≤ H := hfloor
  · have hH0 : (0 : ℝ) ≤ H := by linarith only [hH]
    have hfloor_lt : H < (Nat.floor H : ℝ) + 1 := Nat.lt_floor_add_one H
    have hupperN : Nat.floor H + 1 ≤ 2 ^ (Nat.log2 (Nat.floor H) + 1) :=
      Nat.succ_le_of_lt (Nat.lt_log2_self (n := Nat.floor H))
    have hupper : (Nat.floor H : ℝ) + 1 ≤ (2 : ℝ) ^ (Nat.log2 (Nat.floor H) + 1) := by
      exact_mod_cast hupperN
    exact hfloor_lt.trans_le hupper

/-- Combine quadratic and cubic cardinality budgets across dyadic bands.

Input: Nonnegative band masses `A j`, energy budget `E`, cubic budget
`C*P^3`, and a cutoff `H` between consecutive powers of two. Each band must
satisfy `A j * 2^(2j) ≤ E` and `A j * 2^(3j) ≤ C*P^3`.
Claim: The sum of `2^(2j) * A j^(3/4)` is bounded by the two geometric tails
at the balancing cutoff, with fourth roots represented by nested square roots.
Proof: Use the quadratic budget below the cutoff and the cubic budget above
it, then apply the finite geometric split bound.
Role: Formalizes the band-sum step needed for analysis7 equation (3). -/
theorem dyadic_fourthRoot_sum_le_of_band_budgets {n m : ℕ} {E C P H : ℝ} (hE : 0 ≤ E) (hC : 0 ≤ C)
    (hP : 0 ≤ P) (hlo : (2 : ℝ) ^ m ≤ H) (hhi : H < (2 : ℝ) ^ (m + 1)) (A : ℕ → ℝ)
    (hA : ∀ j, 0 ≤ A j) (hquad : ∀ j, A j * ((2 : ℝ) ^ j) ^ 2 ≤ E)
    (hcube : ∀ j, A j * ((2 : ℝ) ^ j) ^ 3 ≤ C * P ^ 3) :
    (∑ j ∈ Finset.range (n + 1), ((2 : ℝ) ^ j) ^ 2 * (Real.sqrt (Real.sqrt (A j))) ^ 3) ≤
      4 * (Real.sqrt (Real.sqrt E)) ^ 3 * Real.sqrt H +
        7 * (Real.sqrt (Real.sqrt (C * P ^ 3))) ^ 3 * (Real.sqrt (Real.sqrt H))⁻¹ := by
  apply
    sum_split_by_real_cutoff (pow_nonneg (Real.sqrt_nonneg _) 3) (pow_nonneg (Real.sqrt_nonneg _) 3)
      hlo hhi (fun j ↦ ((2 : ℝ) ^ j) ^ 2 * (Real.sqrt (Real.sqrt (A j))) ^ 3)
  · intro j hj
    exact
      dyadicQuarter_low_bound (hA j) (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) j) hE (hquad j)
  · intro j hj
    exact
      dyadicQuarter_cubic_bound (hA j) (pow_pos (by norm_num only : (0 : ℝ) < 2) j) hC hP (hcube j)

/-- The two geometric tails agree at the balancing ratio `B/E`.

Input: Positive real budgets `E` and `B`.
Claim: The low and high fourth-root envelopes at `H = B/E` sum to at most
`16 * E^(1/4) * B^(1/2)`.
Proof: Rewrite both terms using the square-root quotient identities; their
coefficients add to `11`, which is at most `16`.
Role: Converts the cutoff form of the band estimate to its scale-free bound. -/
theorem balanced_fourthRoot_tails_le {E B : ℝ} (hE : 0 < E) (hB : 0 < B) :
    4 * (Real.sqrt (Real.sqrt E)) ^ 3 * Real.sqrt (B / E) +
        7 * (Real.sqrt (Real.sqrt B)) ^ 3 * (Real.sqrt (Real.sqrt (B / E)))⁻¹ ≤
      16 * Real.sqrt (Real.sqrt E) * Real.sqrt B := by
  let qE := Real.sqrt (Real.sqrt E)
  let qB := Real.sqrt (Real.sqrt B)
  have hqE : 0 < qE := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hE)
  have hqB : 0 < qB := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hB)
  have hqEsq : qE ^ 2 = Real.sqrt E := Real.sq_sqrt (Real.sqrt_nonneg E)
  have hqBsq : qB ^ 2 = Real.sqrt B := Real.sq_sqrt (Real.sqrt_nonneg B)
  have hroot : Real.sqrt (B / E) = Real.sqrt B / Real.sqrt E := Real.sqrt_div hB.le E
  have hqroot : Real.sqrt (Real.sqrt B / Real.sqrt E) = qB / qE :=
    Real.sqrt_div (Real.sqrt_nonneg B) (Real.sqrt E)
  have hfirst : 4 * qE ^ 3 * (Real.sqrt B / Real.sqrt E) = 4 * qE * Real.sqrt B := by
    rw [← hqEsq]
    calc
      4 * qE ^ 3 * (Real.sqrt B / qE ^ 2) = 4 * (qE ^ 3 * Real.sqrt B / qE ^ 2) := by ring
      _ = 4 * (qE * Real.sqrt B) := by
        congr 1
        rw [div_eq_iff (ne_of_gt (pow_pos hqE 2))]
        ring
      _ = 4 * qE * Real.sqrt B := by ring
  have hsecond : 7 * qB ^ 3 * (qB / qE)⁻¹ = 7 * qE * Real.sqrt B := by
    rw [inv_div, ← hqBsq]
    calc
      7 * qB ^ 3 * (qE / qB) = 7 * (qB ^ 3 * qE / qB) := by ring
      _ = 7 * (qE * qB ^ 2) := by
        congr 1
        rw [div_eq_iff (ne_of_gt hqB)]
        ring
      _ = 7 * qE * qB ^ 2 := by ring
  rw [hroot, hqroot]
  calc
    4 * qE ^ 3 * (Real.sqrt B / Real.sqrt E) + 7 * qB ^ 3 * (qB / qE)⁻¹ =
        4 * qE * Real.sqrt B + 7 * qE * Real.sqrt B :=
      by rw [hfirst, hsecond]
    _ = 11 * (qE * Real.sqrt B) := by ring
    _ ≤ 16 * qE * Real.sqrt B := by
      have hprod : 0 ≤ qE * Real.sqrt B := mul_nonneg hqE.le (Real.sqrt_nonneg B)
      nlinarith only [hprod]

/-- Sum all dyadic bands at the cutoff selected by the two budgets.

Input: Positive quadratic and cubic budgets, with `E ≤ B`, and per-band
quadratic and cubic constraints.
Claim: The sum of `2^(2j) * A(j)^(3/4)` is at most
`16 * E^(1/4) * B^(1/2)`.
Proof: Choose a dyadic cutoff for `B/E`, apply the two-tail estimate, then
use the exact balance of the tails.
Role: Supplies the band-sum bound in analysis7 without a band-count factor. -/
theorem dyadic_fourthRoot_sum_le_of_balanced_band_budgets {n : ℕ} {E B : ℝ} (hE : 0 < E)
    (hEB : E ≤ B) (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (hquad : ∀ j, A j * ((2 : ℝ) ^ j) ^ 2 ≤ E)
    (hcube : ∀ j, A j * ((2 : ℝ) ^ j) ^ 3 ≤ B) :
    (∑ j ∈ Finset.range (n + 1), ((2 : ℝ) ^ j) ^ 2 * (Real.sqrt (Real.sqrt (A j))) ^ 3) ≤
      16 * Real.sqrt (Real.sqrt E) * Real.sqrt B := by
  have hB : 0 < B := lt_of_lt_of_le hE hEB
  have hH : (1 : ℝ) ≤ B / E := by
    rw [le_div_iff₀ hE]
    simpa only [one_mul] using hEB
  obtain ⟨m, hlo, hhi⟩ := exists_nat_pow_two_cutoff hH
  have hsum :=
    dyadic_fourthRoot_sum_le_of_band_budgets (n := n) (m := m) (E := E) (C := B) (P := 1) (H :=
      B / E) hE.le (le_of_lt hB) (by norm_num only : (0 : ℝ) ≤ 1) hlo hhi A hA hquad
      (by simpa only [one_pow, mul_one] using hcube)
  have htails := balanced_fourthRoot_tails_le hE hB
  exact hsum.trans (by simpa only [one_pow, mul_one] using htails)

end PseudoPrime.Analysis
