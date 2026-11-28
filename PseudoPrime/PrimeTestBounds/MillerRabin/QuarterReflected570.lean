/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerPrefix570

/-! # Signed reflected Euler prefix for the section 31 kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The section 31 reflected Mangoldt moment at exponent 38/25 and logarithmic degree j. -/
noncomputable def reflectedMoment570 (j n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * Real.log n ^ j * (n : ℝ) ^ (-(38 / 25 : ℝ))

/-- A positive exponential Taylor minorant compares each shifted-weight term to finitely
many certified moments at exponent 79/50. -/
private theorem moment_taylor {n : ℕ} (hn : 0 < n) (j m : ℕ) :
    ∑ k ∈ Finset.range m, (3 / 50 : ℝ) ^ k / k.factorial * quarterMangoldtMoment (j + k) n ≤
      reflectedMoment570 j n := by
  have hx : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have he :
    (n : ℝ) ^ (-(79 / 50 : ℝ)) * Real.exp (Real.log n * (3 / 50)) = (n : ℝ) ^ (-(38 / 25 : ℝ)) := by
    rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx, ← Real.exp_add]
    congr 1
    ring
  have ht :=
    Real.sum_le_exp_of_nonneg
      (mul_nonneg (Real.log_natCast_nonneg n) (by norm_num only : (0 : ℝ) ≤ 3 / 50)) m
  have hm := mul_le_mul_of_nonneg_left ht (quarter_mangoldt_moment_nonneg j n)
  rw [Finset.mul_sum] at hm
  unfold reflectedMoment570
  rw [← he, ← mul_assoc]
  apply le_trans (Finset.sum_le_sum (fun k _ ↦ le_of_eq ?_)) hm
  unfold quarterMangoldtMoment
  rw [pow_add, mul_pow]
  ring

/-- The certified finite moment lower bounds through degree five used in the reflected prefix. -/
noncomputable def momentFloor570 : ℕ → ℝ
  | 0 => 1222 / 1000
  | 1 => 2662 / 1000
  | 2 => 8498 / 1000
  | 3 => 35559 / 1000
  | 4 => 176804 / 1000
  | 5 => 981502 / 1000
  | _ => 0

/-- Each tabulated bound through degree five follows from the corresponding kernel certificate. -/
private theorem moment_floor (j : ℕ) (hj : j ≤ 5) :
    momentFloor570 j ≤ ∑ n ∈ Finset.Ioc 0 2701, quarterMangoldtMoment j n := by
  interval_cases j
  · exact quarter_moment_lower_real0
  · exact quarter_moment_lower_real1
  · exact quarter_moment_lower_real2
  · exact quarter_moment_lower_real3
  · exact quarter_moment_lower_real4
  · exact quarter_moment_lower_real5

/-- The improved finite moment bound obtained by Taylor expansion through degree five. -/
noncomputable def reflectedFloor570 (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (6 - j), (3 / 50 : ℝ) ^ k / k.factorial * momentFloor570 (j + k)

/-- For degrees up to five, summation of the Taylor minorant gives the improved lower bound. -/
theorem reflected_moment_lower_570 (j : ℕ) (hj : j ≤ 5) :
    reflectedFloor570 j ≤ ∑ n ∈ Finset.Ioc 0 2701, reflectedMoment570 j n := by
  have ht :=
    Finset.sum_le_sum (s := Finset.Ioc 0 2701)
      (fun n hn ↦ moment_taylor (Finset.mem_Ioc.mp hn).1 j (6 - j))
  rw [Finset.sum_comm] at ht
  simp only [← Finset.mul_sum] at ht
  apply le_trans (Finset.sum_le_sum (fun k hk ↦ ?_)) ht
  have hk' := Finset.mem_range.mp hk
  have he := Nat.sub_add_cancel (Nat.le_trans hj (by decide : 5 ≤ 6))
  have hdeg : j + k ≤ 5 := by linarith only [hk', he]
  exact mul_le_mul_of_nonneg_left (moment_floor (j + k) hdeg) (by positivity)

/-- The reflected Euler summand before multiplication by the common positive kernel factor. -/
noncomputable def reflectedWeight570 (z : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(38 / 25 : ℝ)) * (z + Real.log n) ^ 5

/-- Binomial expansion writes each reflected weight as six logarithmic moments. -/
private theorem reflected_expand (z : ℝ) (n : ℕ) :
    reflectedWeight570 z n =
      ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * z ^ (5 - j) * reflectedMoment570 j n := by
  unfold reflectedWeight570 reflectedMoment570
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
  ring

/-- The binomial polynomial built from the six improved prefix lower bounds. -/
noncomputable def reflectedPrefixFloor570 (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * z ^ (5 - j) * reflectedFloor570 j

/-- For nonnegative shifts the positive binomial coefficients preserve the finite moment bounds. -/
theorem reflected_prefix_lower_570 {z : ℝ} (hz : 0 ≤ z) :
    reflectedPrefixFloor570 z ≤ ∑ n ∈ Finset.Ioc 0 2701, reflectedWeight570 z n := by
  simp only [reflected_expand]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  exact
    mul_le_mul_of_nonneg_left
      (reflected_moment_lower_570 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _))

/-- Each reflected moment is summable by absolute convergence of the logarithmic
Dirichlet series at exponent 38/25. -/
private theorem reflected_summable (j : ℕ) : Summable (reflectedMoment570 j) := by
  have h :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 38 / 25)
      (by norm_num only) j
  apply h.congr
  intro n
  rw [reflectedMoment570, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- The reflected series is summable by its finite expansion in absolutely convergent moments. -/
private theorem weight_summable (z : ℝ) : Summable (reflectedWeight570 z) := by
  simp_rw [show
      reflectedWeight570 z = fun n ↦
        ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * z ^ (5 - j) * reflectedMoment570 j n
      from funext (reflected_expand z)]
  exact summable_sum (fun j _ ↦ (reflected_summable j).mul_left _)

/-- If the real character sum lies in [-1,3] and equals three on the prefix Mangoldt support,
the negative reflected series is bounded by the complementary weight minus three prefix bounds. -/
theorem reflected_signed_upper_570 {z : ℝ} (hz : 0 ≤ z) (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    -(∑' n : ℕ, τ n * reflectedWeight570 z n) ≤
      (∑' n : ℕ, reflectedWeight570 z n) - (∑ n ∈ Finset.Ioc 0 2701, reflectedWeight570 z n) -
        3 * reflectedPrefixFloor570 z := by
  have hw (n : ℕ) : 0 ≤ reflectedWeight570 z n := by
    unfold reflectedWeight570
    have hl := Real.log_natCast_nonneg n
    positivity
  have hs := weight_summable z
  have hsτ : Summable (fun n ↦ τ n * reflectedWeight570 z n) := by
    apply (hs.mul_left 3).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw n)]
    exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith only [(ht n).1], (ht n).2⟩) (hw n)
  have h :=
    (hs.add hsτ).sum_le_tsum (Finset.Ioc 0 2701)
      (fun n _ ↦ by
        have hsign := mul_le_mul_of_nonneg_right (ht n).1 (hw n)
        linarith only [hsign])
  rw [hs.tsum_add hsτ] at h
  have he :
    (∑ n ∈ Finset.Ioc 0 2701, (reflectedWeight570 z n + τ n * reflectedWeight570 z n)) =
      4 * ∑ n ∈ Finset.Ioc 0 2701, reflectedWeight570 z n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h0 : ArithmeticFunction.vonMangoldt n = 0
    · simp only [reflectedWeight570, h0, zero_mul, mul_zero, add_zero]
    · rw [hp n hn h0]
      ring
  change (∑ n ∈ Finset.Ioc 0 2701, (reflectedWeight570 z n + τ n * reflectedWeight570 z n)) ≤ _ at h
  rw [he] at h
  linarith only [h, reflected_prefix_lower_570 hz]

/-- Six complementary moment caps and the certified prefix bounds give the signed
polynomial upper bound in section 31.5 by exchanging the finite and infinite sums. -/
theorem reflected_moment_caps_570 {z : ℝ} (hz : 0 ≤ z) (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) (U : ℕ → ℝ)
    (hU :
      ∀ j ∈ Finset.range 6,
        (∑' n, reflectedMoment570 j n) - (∑ n ∈ Finset.Ioc 0 2701, reflectedMoment570 j n) ≤ U j) :
    -(∑' n : ℕ, τ n * reflectedWeight570 z n) ≤
      ∑ j ∈ Finset.range 6,
        (Nat.choose 5 j : ℝ) * z ^ (5 - j) * (U j - 3 * reflectedFloor570 j) := by
  apply (reflected_signed_upper_570 hz τ ht hp).trans
  simp only [reflected_expand, reflectedPrefixFloor570]
  rw [Summable.tsum_finsetSum (fun j _ ↦ (reflected_summable j).mul_left _),
    Finset.sum_comm (s := Finset.Ioc 0 2701)]
  simp only [tsum_mul_left, ← Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have hm :=
    mul_le_mul_of_nonneg_left (hU j hj)
      (mul_nonneg (Nat.cast_nonneg (Nat.choose 5 j)) (pow_nonneg hz (5 - j)))
  linarith only [hm]

end PseudoPrime.PrimeTestBounds.MillerRabin
