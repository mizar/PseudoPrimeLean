/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevBounds

/-! # Explicit square-root cost for higher prime powers -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A uniform linear upper bound for `psi` gives a three-root bound for `psi - theta`.
Apply the Costa-Pereira inequality before substituting the linear envelope.
Keeping all three powers permits sharper scale-dependent prime-power budgets. -/
theorem psi_sub_theta_le_roots {C x : ℝ} (hx : 0 ≤ x)
    (hpsi : ∀ t : ℝ, 0 ≤ t → Chebyshev.psi t ≤ C * t) :
    Chebyshev.psi x - Chebyshev.theta x ≤
      C * (Real.sqrt x + x ^ (1 / 3 : ℝ) + x ^ (1 / 5 : ℝ)) := by
  have h2 := hpsi (x ^ ((2 : ℝ)⁻¹)) (Real.rpow_nonneg hx _)
  have h3 := hpsi (x ^ ((3 : ℝ)⁻¹)) (Real.rpow_nonneg hx _)
  have h5 := hpsi (x ^ ((5 : ℝ)⁻¹)) (Real.rpow_nonneg hx _)
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  rw [Real.sqrt_eq_rpow]
  norm_num only [one_div] at h2 h3 h5 h ⊢
  nlinarith only [h, h2, h3, h5]

private theorem cube_root_le_three_fifths_sqrt {x : ℝ} (hx : 32 ≤ x) :
    x ^ (1 / 3 : ℝ) ≤ (3 / 5 : ℝ) * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hroot : (5 / 3 : ℝ) ≤ x ^ ((6 : ℝ)⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num) hx0 (by norm_num : (0 : ℝ) < 6)).2
    norm_num only [Real.rpow_ofNat]
    linarith only [hx]
  have hmul := mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg hx0 (1 / 3 : ℝ))
  have he : x ^ ((6 : ℝ)⁻¹) * x ^ (1 / 3 : ℝ) = Real.sqrt x := by
    rw [← Real.rpow_add (by linarith only [hx]), Real.sqrt_eq_rpow]
    norm_num
  rw [he] at hmul
  linarith only [hmul]

private theorem fifth_root_le_two_fifths_sqrt {x : ℝ} (hx : 32 ≤ x) :
    x ^ (1 / 5 : ℝ) ≤ (2 / 5 : ℝ) * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hpow : (5 / 2 : ℝ) ^ 10 ≤ x ^ (3 : ℕ) := by
    calc
      _ ≤ (32 : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ x ^ (3 : ℕ) := by gcongr
  have hroot : (5 / 2 : ℝ) ≤ (x ^ (3 : ℕ)) ^ ((10 : ℝ)⁻¹) := by
    apply
      (Real.le_rpow_inv_iff_of_pos (by norm_num) (pow_nonneg hx0 3) (by norm_num : (0 : ℝ) < 10)).2
    simpa only [Real.rpow_ofNat] using hpow
  have he : (x ^ (3 : ℕ)) ^ ((10 : ℝ)⁻¹) = x ^ (3 / 10 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  rw [he] at hroot
  have hmul := mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg hx0 (1 / 5 : ℝ))
  have he' : x ^ (3 / 10 : ℝ) * x ^ (1 / 5 : ℝ) = Real.sqrt x := by
    rw [← Real.rpow_add (by linarith only [hx]), Real.sqrt_eq_rpow]
    norm_num
  rw [he'] at hmul
  linarith only [hmul]

/-- A nonnegative uniform linear psi bound costs at most twice its coefficient
in the higher-prime-power mass. The fifth-root term vanishes below 32. -/
theorem psi_sub_theta_le_twice_linear_sqrt {C x : ℝ} (hx : 1 ≤ x) (hC : 0 ≤ C)
    (hpsi : ∀ t : ℝ, 0 ≤ t → Chebyshev.psi t ≤ C * t) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 2 * C * Real.sqrt x := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hcp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have h2 := hpsi (x ^ ((2 : ℝ)⁻¹)) (Real.rpow_nonneg hx0 _)
  have h3 := hpsi (x ^ ((3 : ℝ)⁻¹)) (Real.rpow_nonneg hx0 _)
  have hr2 : x ^ ((2 : ℝ)⁻¹) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [hr2] at hcp h2
  by_cases hsmall : x < 32
  · have hr5 : x ^ ((5 : ℝ)⁻¹) < 2 := by
      apply (Real.rpow_inv_lt_iff_of_pos hx0 (by norm_num) (by norm_num : (0 : ℝ) < 5)).2
      simpa only [Real.rpow_ofNat, show (2 : ℝ) ^ (5 : ℕ) = 32 by norm_num] using hsmall
    rw [Chebyshev.psi_eq_zero_of_lt_two hr5, add_zero] at hcp
    have hr3 : x ^ ((3 : ℝ)⁻¹) ≤ Real.sqrt x := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    have hm := mul_le_mul_of_nonneg_left hr3 hC
    linarith only [hcp, h2, h3, hm]
  · have hx32 : 32 ≤ x := le_of_not_gt hsmall
    have h5 := hpsi (x ^ ((5 : ℝ)⁻¹)) (Real.rpow_nonneg hx0 _)
    have hr3 := cube_root_le_three_fifths_sqrt hx32
    have hr5 := fifth_root_le_two_fifths_sqrt hx32
    norm_num only [one_div] at hr3 hr5
    have hm3 := mul_le_mul_of_nonneg_left hr3 hC
    have hm5 := mul_le_mul_of_nonneg_left hr5 hC
    nlinarith only [hcp, h2, h3, h5, hm3, hm5]

/-- For x at least one, higher prime powers have Mangoldt mass at most `6 sqrt x`.
Apply the common linear psi bound to the two-coefficient Costa-Pereira estimate.
No RH or finite prime table is needed. -/
theorem psi_sub_theta_le_six_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 6 * Real.sqrt x := by
  have h :=
    psi_sub_theta_le_twice_linear_sqrt hx (by norm_num : (0 : ℝ) ≤ 3) (fun _ ht => psi_le_three ht)
  norm_num only [show (2 : ℝ) * 3 = 6 by norm_num] at h
  exact h

/-- For x ≥ 1 and arbitrary real weights at most 1/3, twice the weighted
nonprime Mangoldt mass is at most 4sqrt x. Compare termwise and use the exact
psi-theta decomposition. This is the cubic higher-prime-power defect interface. -/
theorem composite_mangoldt_weight_le_four_sqrt {x : ℝ} (hx : 1 ≤ x) (w : ℕ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, w n ≤ 1 / 3) :
    (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬n.Prime),
        2 * ArithmeticFunction.vonMangoldt n * w n) ≤
      4 * Real.sqrt x := by
  have ht :
    (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬n.Prime),
        2 * ArithmeticFunction.vonMangoldt n * w n) ≤
      (2 / 3 : ℝ) *
        ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬n.Prime), ArithmeticFunction.vonMangoldt n := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have h :=
      mul_le_mul_of_nonneg_left (hw n (Finset.mem_filter.mp hn).1)
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2)
          (ArithmeticFunction.vonMangoldt_nonneg (n := n)))
    nlinarith only [h]
  rw [← Chebyshev.psi_sub_theta_eq_sum_not_prime] at ht
  linarith only [ht, psi_sub_theta_le_six_sqrt hx]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
